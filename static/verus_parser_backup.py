import os, sys
import hashlib
from tqdm import tqdm
from utils import *
import tree_sitter
from tree_sitter import Language, Parser

def node_to_text(node:tree_sitter.Node) -> str:
    return node.text.decode()
    
class verus_parser:
    def __init__(self, language_path:str) -> None:
        self.language = Language(language_path, 'rust')
        self.parser = Parser()
        self.parser.set_language(self.language)
    
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

    def extract_function(self, program:tree_sitter.Node):
        query = self.language.query('(function_item) @function_item')
        functions = [node for node, name in query.captures(program)]
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

def spec_compatible(src_prog: str, dst_prog: str, language_path: str) -> bool:
    src_editor = verus_editor(src_prog, language_path)
    src_editor.remove_proof()
    src_editor.remove_comment()
    src_hash = src_editor.vs_parser.get_tree_hash(src_editor.current_ast.root_node)

    dst_editor = verus_editor(dst_prog, language_path)
    dst_editor.remove_proof()
    dst_editor.remove_comment()
    dst_hash = dst_editor.vs_parser.get_tree_hash(dst_editor.current_ast.root_node)

    return src_hash == dst_hash

def test_spec_compatible():
    verus_bench = load_json('/home/v-tianychen/data/for_train/verus_sft_test_v2.json')
    # cnt = 0
    # for idx, task in enumerate(verus_bench):
    #     src_prog = remove_symbol(task['verus_spec'])
    #     dst_prog = remove_symbol(task['verus_proof'])
    #     compatible = spec_compatible(src_prog, dst_prog)
    #     if not compatible:
    #         src_editor = verus_editor(src_prog)
    #         src_editor.remove_proof()
    #         src_editor.remove_comment()
    #         src_hash = src_editor.vs_parser.get_tree_hash(src_editor.current_ast.root_node)
    #         dst_editor = verus_editor(dst_prog)
    #         dst_editor.remove_proof()
    #         dst_editor.remove_comment()
    #         dst_hash = dst_editor.vs_parser.get_tree_hash(dst_editor.current_ast.root_node)
    #         cnt = cnt + 1
    #         print(idx, src_hash, dst_hash, '\n-------\n')
    #         # if cnt == 4:
    #         print(src_editor.current_program, '\n-------\n', dst_editor.current_program)
    #         print('\n-------\n', dst_prog)
    compatibles = [spec_compatible(task['verus_spec'], task['verus_proof']) \
                    for task in verus_bench]
    print(sum(compatibles), len(compatibles))

def get_proof_fn_spec_groups(proof_fn_spec_node: tree_sitter.Node):
    SPEC_KWORDS = [
        'requires',
        'ensures',
        'decreases',
        'recommends',
    ]
    spec_groups = {}
    cur_kword = None
    if proof_fn_spec_node is None:
        return spec_groups
    for child in proof_fn_spec_node.children:
        if child.type in SPEC_KWORDS:
            cur_kword = child.type
            spec_groups[cur_kword] = []
        spec_groups[cur_kword].append(child)
    return spec_groups

def remove_decreases(editor: verus_editor, proof_fn_spec_node: tree_sitter.Node):
    '''
    Remove increases and decreases specifications from the proof function specification node.
    '''
    spec_groups = get_proof_fn_spec_groups(proof_fn_spec_node)
    if 'decreases' in spec_groups:
        editor.replace_nodes(spec_groups['decreases'], target_str='')

def proof_fn_spec_compatible(src_prog: str, dst_prog: str, language_path: str) -> bool:
    '''
    Check if the proof function specifications in src_prog and dst_prog are compatible.
    Compatibility means that:
    1. All proof functions in src_prog exist in dst_prog.
    2. The specifications of the proof functions in src_prog and dst_prog are the same.
    3. The proof functions in dst_prog have the same specifications as the proof functions in src_prog.
    '''
    src_editor = verus_editor(src_prog, language_path)
    src_editor.remove_proof_with_body()
    src_editor.remove_comment()
    proof_function_names = []
    src_proof_fns = {}
    for fn in src_editor.vs_parser.extract_proof_fn(src_editor.current_ast.root_node):
        remove_decreases(src_editor, fn.child_by_field_name('specifications'))
    for fn in src_editor.vs_parser.extract_proof_fn(src_editor.current_ast.root_node):
        fn_name = fn.child_by_field_name('name').text.decode()
        proof_function_names.append(fn_name)
        src_proof_fns[fn_name] = src_editor.vs_parser.get_tree_hash(fn)

    dst_editor = verus_editor(dst_prog, language_path)
    dst_editor.remove_proof_with_body()
    dst_editor.remove_comment()
    dst_proof_fns = {}
    for fn in dst_editor.vs_parser.extract_proof_fn(dst_editor.current_ast.root_node):
        remove_decreases(dst_editor, fn.child_by_field_name('specifications'))
    for fn in dst_editor.vs_parser.extract_proof_fn(dst_editor.current_ast.root_node):
        fn_name = fn.child_by_field_name('name').text.decode()
        if fn_name in proof_function_names:
            dst_proof_fns[fn_name] = dst_editor.vs_parser.get_tree_hash(fn)
        else:
            dst_editor.replace_nodes([fn], target_str='')
    return all([fn_name in dst_proof_fns.keys() for fn_name in src_proof_fns.keys()]) and all([src_proof_fns[fn_name] == dst_proof_fns[fn_name] for fn_name in src_proof_fns.keys()])

def prog_has_assume(prog: str, language_path: str) -> bool:
    """
    Check if the given program contains any assume statements at AST level.
    """
    prog_editor = verus_editor(prog, language_path)
    assumes = prog_editor.vs_parser.extract_assumption(prog_editor.current_ast.root_node)
    return len(assumes) > 0

def prog_has_admit(prog: str, language_path: str) -> bool:
    """
    Check if the given program contains any admit statements at AST level.
    """
    prog_editor = verus_editor(prog, language_path)
    admits = prog_editor.vs_parser.extract_admits(prog_editor.current_ast.root_node)
    return len(admits) > 0

def test_case_spec_compatible():
    with open('/home/v-tianychen/scripts/src_cmp.rs', 'r') as f:
        src_prog = f.read()
    with open('/home/v-tianychen/scripts/dst_cmp.rs', 'r') as f:
        dst_prog = f.read()
    print(spec_compatible(src_prog, dst_prog))

def test_case_proof_fn_spec_compatible():
    import rich
    tests = [
        (2, 16, "true", True),
        (6, 2, 'false', False),
        (7, 30, 'false', False),
        (16, 6, "true", True),
        # (12, 60, "false", False),
        # (14, 72, "false", False),
        (20, 0, 'false', False),
        (20, 5, "true", True),
        (20, 6, "true", True),
        (20, 9, "true", True),
        (21, 26, "true", True),
        (41, 75, "true", True),
        (43, 10, "true", True),
        (55, 35, "true", True),
        (57, 9, "true, use another proof fn as lemma in proof", True),
        (71, 1, "true", True),
        (71, 22, "true", True),
        (71, 38, "true", True),
        (71, 40, "true", True),
        (73, 97, "true", True),
        (77, 66, 'false', False),
        (77, 67, 'false', False),
        (77, 94, 'false', False),
        (78, 20, 'false', False),
        (78, 97, 'false', False),
        (57, 88, "true, add a decrease in proof fn, can be used in proof", True),
    ]
    for test in tests:
        input_idx, pred_index, test_info, result_gt = test
        print(f'Current test: {input_idx}, {pred_index}, {test_info}')
        with open(f'/home/v-nongyudi/gits/llm-notes/msra/verus/checker/extracted_samples/0805_eval_on-memory-allocator-unverified-nolemmaeval_direct_gen_results/sample_{input_idx}_input.rs', 'r') as f:
            src_prog = f.read()
        with open(f'/home/v-nongyudi/gits/llm-notes/msra/verus/checker/extracted_samples/0805_eval_on-memory-allocator-unverified-nolemmaeval_direct_gen_results/sample_{input_idx}_prediction_{pred_index}_no_loop_correct.rs', 'r') as f:
            dst_prog = f.read()
        result = proof_fn_spec_compatible(src_prog, dst_prog, '/home/v-nongyudi/verus.so')
        # print(result)
        print(f'Current result: {result}, ground truth: {result_gt}')
        assert result == result_gt, f"Test failed for input {input_idx}, prediction {pred_index}, expected {result_gt}, got {result}"
        print("Test passed!")

if __name__ == '__main__':
    # verified_storage_pipeline()
    # test_spec_compatible()
    # test_case_spec_compatible()
    # test_case_proof_fn_spec_compatible()
    pass