import os, sys
import ctypes
import hashlib

from tqdm import tqdm
from utils import *
import tree_sitter
from tree_sitter import Language, Parser, QueryCursor, Query

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
    
    def extract_function(self, program:tree_sitter.Node, target_modes:str=[], skip_external=False):
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
    
    # tbd: merge with extract_function
    
    def extract_function_modifiers(self, function:tree_sitter.Node) -> str:
        query = self.language.query('(function_modifiers) @function_modifiers')
        modifiers = [node for node, name in query.captures(function)] # zero/one captures
        if len(modifiers) == 0:
            modifier_names = []
        else:
            modifier_names = [node_to_text(modifier_node) \
                              for modifier_node in modifiers[0].children]
        return modifier_names

    def extract_specification(self, function:tree_sitter.Node,
                              types):
        specifications = function.child_by_field_name('specifications')
        if specifications is None:
            specifications = []
        return specifications

    def extract_spec_fn(self, program:tree_sitter.Node):
        query = self.language.query(
            '(attribute_item)@attribute_item (function_item) @function_item')

        last_attribute = False
        included_functions = []
        for node, name in query.captures(program):
            if name == 'attribute_item':
                last_attribute = last_attribute or \
                    node_to_text(node.named_children[0]) == 'verifier::external_body'
            elif last_attribute:
                    last_attribute = False
            else:
                included_functions.append(node)
        modifier_lists = [self.extract_function_modifiers(function_node) \
                          for function_node in included_functions]
        spec_functions = [function for function, modifiers in \
                           zip(included_functions, modifier_lists) if 'spec' in modifiers]
        return spec_functions

    def extract_proof_fn(self, program:tree_sitter.Node):
        query = self.language.query(
            '(attribute_item)@attribute_item (function_item) @function_item')

        last_attribute = False
        included_functions = []
        for node, name in query.captures(program):
            if name == 'attribute_item':
                last_attribute = last_attribute or \
                    node_to_text(node.named_children[0]) == 'verifier::external_body'
            elif last_attribute:
                    last_attribute = False
            else:
                included_functions.append(node)
        modifier_lists = [self.extract_function_modifiers(function_node) \
                          for function_node in included_functions]
        proof_functions = [function for function, modifiers in \
                           zip(included_functions, modifier_lists) if 'proof' in modifiers]
        return proof_functions

    def extract_function(self, program:tree_sitter.Node, function_mode:list=None):
        declaration_with_attrs_query = self.language.query(
            '(declaration_with_attrs)@declaration_with_attrs')
        declaration_with_attrs = [node for node, name in    
                                    declaration_with_attrs_query.captures(program)]
        # tbd

        query = self.language.query('(function_item) @function_item')
        functions = [node for node, name in query.captures(program)]
        if function_mode is not None:
            functions = [function for function in functions if any(modifier in function_mode for modifier in self.extract_function_modifiers(function))]
        return functions

    def extract_raw_function(self, program:tree_sitter.Node):
        query = self.language.query('(function_item) @function_item')
        functions = [node for node, name in query.captures(program)]
        modifier_lists = [self.extract_function_modifiers(function_node) \
                          for function_node in functions]
        raw_functions = [function for function, modifiers in \
                           zip(functions, modifier_lists) if 'spec' not in modifiers and 'proof' not in modifiers]
        return raw_functions

    def extract_loop_invariant(self, program:tree_sitter.Node):
        query = self.language.query('(loop_specifications) @specifications')
        specifications = [node for node, name in query.captures(program)]
        invariants = [children for expr in specifications \
                      for spec in expr.children \
                      for children in spec.children_by_field_name('invariant')]
        return invariants

    def extract_decreases(self, program:tree_sitter.Node):
        query = self.language.query('[(function_specifications) (loop_specifications)] @specifications')
        specifications = [node for node, name in query.captures(program)]
        decreases = [children for expr in specifications \
                      for spec in expr.children \
                      for children in spec.children_by_field_name('decreases')]
        return decreases

    def extract_proof_block(self, program:tree_sitter.Node):
        query = self.language.query('(proof_block) @proof_block')
        proof_blocks = [node for node, name in query.captures(program)]
        return proof_blocks

    def extract_assertion(self, program:tree_sitter.Node):
        query = self.language.query('(expression_statement) @expression_statement')
        statements = [node for node, name in query.captures(program)]
        assertions = [stmt for stmt in statements \
                      if node_to_text(stmt).strip().startswith('assert')]
        return assertions

    def extract_reveal(self, program:tree_sitter.Node):
        query = self.language.query('(expression_statement) @expression_statement')
        statements = [node for node, name in query.captures(program)]
        reveals = [stmt for stmt in statements \
                    if len(stmt.children) > 0 and \
                        stmt.children[0].type == 'call_expression' and \
                        stmt.children[0].child_by_field_name('function') is not None and \
                        node_to_text(stmt.children[0].child_by_field_name('function')).strip() in ['reveal', 'reveal_with_fuel']]
        return reveals

    def extract_assumption(self, program:tree_sitter.Node):
        query = self.language.query('(call_expression) @call_expression')
        statements = [node for node, name in query.captures(program)]
        assumptions = [stmt for stmt in statements \
                    if len(stmt.children) > 0 and \
                        stmt.child_by_field_name('function') is not None and \
                        node_to_text(stmt.child_by_field_name('function')).strip() == 'assume']
        return assumptions

    def extract_admits(self, program:tree_sitter.Node):
        query = self.language.query('(call_expression) @call_expression')
        statements = [node for node, name in query.captures(program)]
        admits = [stmt for stmt in statements \
                    if len(stmt.children) > 0 and \
                        stmt.child_by_field_name('function') is not None and \
                        node_to_text(stmt.child_by_field_name('function')).strip() == 'admit']
        return admits

    def extract_empty_statements(self, program:tree_sitter.Node):
        query = self.language.query('(empty_statement) @empty_statement')
        empty_statements = [node for node, name in query.captures(program)]
        return empty_statements

    def extract_comment(self, program:tree_sitter.Node):
        query = self.language.query('(block_comment)@block_comment (line_comment) @line_comment')
        comments = [node for node, name in query.captures(program)]
        return comments
    
    def get_tree_hash(self, program:tree_sitter.Node) -> str:
        '''
        Hash(node) = Hash(current_node + \cat_{child_node \in childs} Hash(child_node))
        '''
        try:
            children_hash_list = [self.get_tree_hash(child_node) for child_node in filter(lambda x: len(node_to_text(x)) > 1, program.children)]
            children_hash_list = [h for h in children_hash_list if len(h) > 0]
            children_hash = ' '.join(children_hash_list).strip()
            
            leaf_node = len(program.children) == 0
            if leaf_node:
                node_representation = node_to_text(program)
            else:
                node_representation = program.type + children_hash
            node_hash = hashlib.md5(node_representation.encode()).hexdigest()

            # special cases
            if program.type == 'use_declaration':
                node_hash = ''
            if program.type == 'attribute_item' or program.type == 'inner_attribute_item':
                node_hash = ''
            if program.type == 'let_declaration':
                if sum([node_to_text(child) == 'ghost' for child in program.children]) > 0:
                    node_hash = ''
            if program.type == 'call_expression':
                if node_to_text(program).strip().startswith('reveal'):
                    node_hash = ''
            if not leaf_node and children_hash == '':
                node_hash = ''
        except RecursionError as e:
            node_hash = ''
        return node_hash

class verus_editor:
    def __init__(self, raw_program:str,
                 language_path:str) -> None:
        self.vs_parser = verus_parser(language_path=language_path)
        if '```rust' in raw_program:
            self.raw_program = remove_symbol(raw_program)
        else:
            self.raw_program = raw_program
        self.current_program = self.raw_program
        self.raw_ast = self.vs_parser.parser.parse(bytes(self.raw_program, "utf8"))
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
        self.current_ast = self.vs_parser.parser.parse(bytes(self.current_program, "utf8"))
        return self.current_program

    def remove_comment(self) -> None:
        comments = self.vs_parser.extract_comment(self.current_ast.root_node)
        self.replace_nodes(comments, target_str='')

    def remove_proof_with_body(self) -> None:
        invariants = self.vs_parser.extract_loop_invariant(self.current_ast.root_node)
        self.replace_nodes(invariants, target_str='')

        decreases = self.vs_parser.extract_decreases(self.current_ast.root_node)
        self.replace_nodes(decreases, target_str='')
        
        proofs = self.vs_parser.extract_proof_block(self.current_ast.root_node)
        self.replace_nodes(proofs, target_str='')

        assertions = self.vs_parser.extract_assertion(self.current_ast.root_node)
        self.replace_nodes(assertions, target_str='')

        assumptions = self.vs_parser.extract_assumption(self.current_ast.root_node)
        self.replace_nodes(assumptions, target_str='')

        admits = self.vs_parser.extract_admits(self.current_ast.root_node)
        self.replace_nodes(admits, target_str='')

        reveals = self.vs_parser.extract_reveal(self.current_ast.root_node)
        self.replace_nodes(reveals, target_str='')

        empty_statements = self.vs_parser.extract_empty_statements(self.current_ast.root_node)
        self.replace_nodes(empty_statements, target_str='')

        proof_fns = self.vs_parser.extract_proof_fn(self.current_ast.root_node)
        proof_bodies = [fn.child_by_field_name('body') for fn in proof_fns \
                        if fn.child_by_field_name('body')]

        proof_fn_prompt = '{\n // please add proof here. \n}'
        self.replace_nodes(proof_bodies, target_str=proof_fn_prompt)

    def remove_proof(self) -> None:
        proof_fns = self.vs_parser.extract_proof_fn(self.current_ast.root_node)
        self.replace_nodes(proof_fns, target_str='')

        invariants = self.vs_parser.extract_loop_invariant(self.current_ast.root_node)
        self.replace_nodes(invariants, target_str='')

        decreases = self.vs_parser.extract_decreases(self.current_ast.root_node)
        self.replace_nodes(decreases, target_str='')

        proofs = self.vs_parser.extract_proof_block(self.current_ast.root_node)
        self.replace_nodes(proofs, target_str='')

        assertions = self.vs_parser.extract_assertion(self.current_ast.root_node)
        self.replace_nodes(assertions, target_str='')

        assumptions = self.vs_parser.extract_assumption(self.current_ast.root_node)
        self.replace_nodes(assumptions, target_str='')

        admits = self.vs_parser.extract_admits(self.current_ast.root_node)
        self.replace_nodes(admits, target_str='')

        reveals = self.vs_parser.extract_reveal(self.current_ast.root_node)
        self.replace_nodes(reveals, target_str='')

        empty_statements = self.vs_parser.extract_empty_statements(self.current_ast.root_node)
        self.replace_nodes(empty_statements, target_str='')

    def remove_body(self) -> None:
        functions = self.vs_parser.extract_raw_function(self.current_ast.root_node)
        bodies = [fn.child_by_field_name('body') for fn in functions if 'fn main()' not in node_to_text(fn)]
        self.replace_nodes(bodies, target_str='{\n // please add implementation and proof here. \n}')



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
            storage_benchs.append({'name': file_path, 'input': editor.current_program, 'output': test_rs})
    dump_json(storage_benchs, '/home/v-tianychen/data/append/verified_storage_1209.json')



if __name__ == '__main__':
    return