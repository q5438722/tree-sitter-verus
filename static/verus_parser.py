import os, sys
import ctypes
import hashlib

from tqdm import tqdm
import tree_sitter
from tree_sitter import Language, Parser, QueryCursor, Query

def node_to_text(node) -> str:
    return node.text.decode()

class verus_parser:
    def __init__(self, language_path:str) -> None:
        lib = ctypes.cdll.LoadLibrary(language_path)
        lang_func = lib.tree_sitter_verus
        lang_func.restype = ctypes.c_void_p
        ptr = lang_func()

        self.language = Language(ptr)
        self.parser = Parser(self.language)

    def capture_query(self, program:tree_sitter.Node, query_str:str):
        query = Query(self.language, query_str)
        query_curser = QueryCursor(query)
        res = query_curser.captures(program)
        return res
        
    def match_query(self, program:tree_sitter.Node, query_str:str):
        query = Query(self.language, query_str)
        query_curser = QueryCursor(query)
        res = query_curser.matches(program)
        return [val for idx, val in res]
    
    def extract_functions(self, program:tree_sitter.Node, target_modes:str=[], skip_external=False):
        query_str = '''
            (declaration_with_attrs
                (function_item)@function_item
            )@declaration_with_attrs
            '''
        declaration_matches = self.match_query(program, query_str)

        target_functions = []
        for match in declaration_matches:
            declaration = match['declaration_with_attrs'][0]
            function = match['function_item'][0]
            attributes = [child for child in declaration.children \
                          if child.type == 'attribute_item']
            if skip_external and any('verifier::external_body' in node_to_text(attr) for attr in attributes):
                continue
            function_modes = [node_to_text(child) for child in function.children \
                          if child.type == 'function_mode']
            if target_modes and len(set(function_modes) & set(target_modes))== 0:
                continue
            target_functions.append(declaration)
        return target_functions

    def extract_exec_functions(self, program:tree_sitter.Node, skip_external=False):
        query_str = '''
            (declaration_with_attrs
                (function_item)@function_item
            )@declaration_with_attrs
            '''
        declaration_matches = self.match_query(program, query_str)

        target_functions = []
        for match in declaration_matches:
            declaration = match['declaration_with_attrs'][0]
            function = match['function_item'][0]
            attributes = [child for child in declaration.children \
                          if child.type == 'attribute_item']
            if skip_external and any('verifier::external_body' in node_to_text(attr) for attr in attributes):
                continue
            function_modes = [node_to_text(child) for child in function.children \
                          if child.type == 'function_mode']
            if any(item in ['proof', 'spec'] for item in function_modes):
                continue
            target_functions.append(declaration)
        return target_functions

    def extract_comments(self, program:tree_sitter.Node):
        query_str = '(block_comment)@block_comment (line_comment)@line_comment'
        comment_captures = self.capture_query(program, query_str)
        comments = [node for key, nodes in comment_captures.items() for node in nodes]
        comments.sort(key=lambda x: x.start_byte)
        return comments

    def extract_loop_annotations(self, program:tree_sitter.Node, target_clause=None):
        annotation_types = ['invariant_clause', 'invariant_ensures_clause',
                           'invariant_except_break_clause', 'ensures_clause', 'decreases_clause']
        if target_clause is None:
            target_clause = annotation_types
        
        query_str = '''
        (while_expression)@while_expression 
        (for_expression) @for_expression
        (loop_expression)@loop_expression
        '''
        loop_captures = self.capture_query(program, query_str)
        loop_annotations = [child for key, loops in loop_captures.items() \
                            for loop in loops for child in loop.children \
                            if child.type in target_clause]
        return loop_annotations

    def extract_specific_calls(self, program:tree_sitter.Node, prefixes:list=[]):
        query_str = '(call_expression)@call_expression'
        captures = self.capture_query(program, query_str)
        function_nodes = [node for key, nodes in captures.items() for node in nodes]
        result_functions = [func for func in function_nodes \
                            if any(node_to_text(func.child_by_field_name(
                            'function')).startswith(prefix) for prefix in prefixes)]
        return result_functions
    
    def extract_specific_nodes(self, program:tree_sitter.Node, node_types:list=[]):
        query_str = '\n'.join(f'({node_type})@{node_type}' for node_type in node_types)
        captures = self.capture_query(program, query_str)
        result_nodes = [node for key, nodes in captures.items() for node in nodes]
        return result_nodes

    def extract_specifications(self, program:tree_sitter.Node):
        spec_fns = self.extract_functions(program=program, target_modes=['spec'], skip_external=False)
        fn_qualifiers = self.extract_specific_nodes(program=program, node_types=['fn_qualifier'])
        specs = spec_fns + fn_qualifiers
        return specs
    
    def extract_proofs(self, program:tree_sitter.Node):
        proof_fns = self.extract_functions(program=program, target_modes=['proof'], skip_external=False)
        loop_annotations = self.extract_loop_annotations(program=program)
        proof_blocks = self.extract_specific_nodes(program=program, node_types=['proof_block'])
        
        proof_expr_types = ['assert_expression', 'assume_expression',
                           'assert_by_expression', 'assert_by_block_expression',
                           'assert_forall_expression', 'assert_macro_call']
        proof_exprs = self.extract_specific_nodes(program=program, node_types=proof_expr_types)
        extra_proof_exprs = self.extract_specific_calls(program=program, prefixes=['admit', 'reveal'])

        proofs = proof_fns + loop_annotations + proof_blocks +\
                proof_exprs + extra_proof_exprs
        return proofs
    
    def extract_external(self, program:tree_sitter.Node):
        query_str = '''
            (declaration_with_attrs
                (attribute_item)@attribute_item
            )@declaration_with_attrs
            '''
        declaration_matches = self.match_query(program, query_str)
        external_declarations = [match['declaration_with_attrs'][0] for match in declaration_matches \
                                 if 'verifier::external_body' in node_to_text(match['attribute_item'][0])]
        return external_declarations

    def get_tree_hash(self, program:tree_sitter.Node) -> str:
        '''
        Hash(node) = Hash(current_node + cat_{child_node in childs} Hash(child_node))
        '''
        try:
            children_filter = filter(lambda x: len(node_to_text(x)) > 1, program.children)
            children_hash_list = [self.get_tree_hash(child_node) for child_node in children_filter]
            children_hash_list = [h for h in children_hash_list if len(h) > 0]
            children_hash = ' '.join(children_hash_list).strip()
            
            if len(children_hash) == 0:
                node_representation = node_to_text(program)
            else:
                node_representation = program.type + children_hash
            node_hash = hashlib.md5(node_representation.encode()).hexdigest()
            # move special cases into spec/proof detection.
            if len(children_hash) != 0 and children_hash == '': # not sure whether to keep
                node_hash = ''
        except RecursionError as e:
            node_hash = ''
        return node_hash



class verus_editor:
    def __init__(self, raw_program:str,
                 language_path:str) -> None:
        self.vs_parser = verus_parser(language_path=language_path)
        
        self.raw_program = raw_program
        self.current_program = self.raw_program
        
        self.raw_ast = self.vs_parser.parser.parse(bytes(self.raw_program, "utf-8")).root_node
        self.current_ast = self.raw_ast

    def merge_brackets(self, brackets):
        brackets.sort(key=lambda x: x[0])
        merged_brackets = []
        for idx, bracket in enumerate(brackets):
            current_l, current_r = bracket
            if len(merged_brackets) > 0:
                last_l, last_r = merged_brackets[-1]
                if current_l <= last_r:
                    merged_brackets[-1] = (last_l, max(current_r, last_r))
                    continue
            merged_brackets.append((current_l, current_r))
        return merged_brackets
    
    def replace_nodes(self, nodes, target_str=''):
        new_program = bytes(self.current_program, encoding='utf-8')
        replace_brackets = [(node.start_byte, node.end_byte) for node in nodes]
        replace_brackets = self.merge_brackets(replace_brackets)
        replace_brackets.sort(key=lambda x: x[0], reverse=True)
        for l, r in replace_brackets:
            new_program = new_program[:l] + bytes(target_str, encoding='utf-8') + new_program[r:]
        self.current_program = new_program.decode()
        self.current_ast = self.vs_parser.parser.parse(bytes(self.current_program, 'utf-8')).root_node
        return self.current_program

    def clean_program(self):
        empty_nodes = self.vs_parser.extract_specific_nodes(program=self.current_ast,
                                                            node_types=['empty_statement'])
        self.replace_nodes(empty_nodes, '')

    def remove_comment(self) -> None:
        comments = self.vs_parser.extract_comments(self.current_ast)
        self.replace_nodes(comments, target_str='')

    def remove_specification(self) -> None:
        specifications = self.vs_parser.extract_specifications(self.current_ast)
        self.replace_nodes(specifications, target_str='')
    
    def remove_proof(self) -> None:
        proofs = self.vs_parser.extract_proofs(self.current_ast)
        self.replace_nodes(proofs, target_str='')

    def remove_external(self) -> None:
        external_declarations = self.vs_parser.extract_external(self.current_ast)
        self.replace_nodes(external_declarations, target_str='')

    def remove_body(self) -> None:
        functions = self.vs_parser.extract_functions(self.current_ast)
        bodies = [fn.child_by_field_name('body') for fn in functions if 'fn main()' not in node_to_text(fn)]
        bodies = [b for b in bodies if b is not None]
        self.replace_nodes(bodies, target_str='{\n // please add implementation and proof here. \n}')

def spec_compatible(src_prog:str, dst_prog:str, language_path:str) -> bool:
    src_editor = verus_editor(src_prog, language_path)
    src_editor.remove_proof()
    src_editor.remove_comment()
    src_editor.remove_external()
    src_hash = src_editor.vs_parser.get_tree_hash(src_editor.current_ast)

    dst_editor = verus_editor(dst_prog, language_path)
    dst_editor.remove_proof()
    dst_editor.remove_comment()
    dst_editor.remove_external()
    dst_hash = dst_editor.vs_parser.get_tree_hash(dst_editor.current_ast)

    return src_hash == dst_hash

# tbd
def verified_storage_pipeline():
    folder = '/home/v-tianychen/Verus_Copilot/benchmarks/verified-storage/benchmarks'
    files = []
    for step in os.listdir(folder):
        next_folder = os.path.join(folder, step)
        if os.path.isdir(next_folder):
            files = files + [os.path.join(next_folder, case) \
                        for case in os.listdir(next_folder) if case.endswith('.rs')]
    storage_benchs = []
    for file_path in tqdm(files):
        if os.path.exists(file_path):
            with open(file_path, 'r') as f:
                test_rs = f.read()
            editor = verus_editor(test_rs)
            editor.remove_proof_with_body()
            editor.remove_external()
            storage_benchs.append({'name': file_path, 'input': editor.current_program, 'output': test_rs})
    dump_json(storage_benchs, '/home/v-tianychen/data/append/verified_storage_1209.json')
