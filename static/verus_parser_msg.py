import os, sys
import hashlib
from difflib import SequenceMatcher
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
        Hash(node) = Hash(current_node + cat {child_node in childs} Hash(child_node))
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

def _collect_tree_diffs(vs_parser, src_node, dst_node, diffs):
    """
    Recursively compare two AST nodes using tree hashes (bottom-to-top).
    Drills into children to find the most specific (deepest) differing
    node pairs, effectively comparing from bottom to top.

    Args:
        vs_parser: verus_parser instance for hash computation.
        src_node: source AST node.
        dst_node: destination AST node.
        diffs: list to collect (diff_type, src_node, dst_node) tuples.
               diff_type is 'modify', 'delete', or 'insert'.
    """
    src_hash = vs_parser.get_tree_hash(src_node)
    dst_hash = vs_parser.get_tree_hash(dst_node)

    if src_hash == dst_hash:
        return
    if src_hash == '' and dst_hash == '':
        return

    # Get meaningful children (same filtering as get_tree_hash)
    src_children = [c for c in src_node.children
                    if len(node_to_text(c)) > 1 and vs_parser.get_tree_hash(c) != '']
    dst_children = [c for c in dst_node.children
                    if len(node_to_text(c)) > 1 and vs_parser.get_tree_hash(c) != '']

    if not src_children and not dst_children:
        diffs.append(('modify', src_node, dst_node))
        return
    if not src_children or not dst_children:
        diffs.append(('modify', src_node, dst_node))
        return

    # Align children using hash-based sequence matching
    src_hashes = [vs_parser.get_tree_hash(c) for c in src_children]
    dst_hashes = [vs_parser.get_tree_hash(c) for c in dst_children]

    matcher = SequenceMatcher(None, src_hashes, dst_hashes)

    has_child_diff = False
    for op, i1, i2, j1, j2 in matcher.get_opcodes():
        if op == 'equal':
            continue
        has_child_diff = True
        if op == 'replace':
            min_len = min(i2 - i1, j2 - j1)
            for k in range(min_len):
                _collect_tree_diffs(vs_parser,
                                    src_children[i1 + k],
                                    dst_children[j1 + k], diffs)
            for si in range(i1 + min_len, i2):
                diffs.append(('delete', src_children[si], None))
            for di in range(j1 + min_len, j2):
                diffs.append(('insert', None, dst_children[di]))
        elif op == 'delete':
            for si in range(i1, i2):
                diffs.append(('delete', src_children[si], None))
        elif op == 'insert':
            for di in range(j1, j2):
                diffs.append(('insert', None, dst_children[di]))

    if not has_child_diff:
        diffs.append(('modify', src_node, dst_node))

def _find_enclosing_function_name(vs_parser, root_node, byte_offset):
    """
    Find the name of the innermost enclosing function for a byte offset.
    Returns '<top-level>' if no enclosing function is found.
    """
    functions = vs_parser.extract_function(root_node)
    best_fn = None
    for fn in functions:
        if fn.start_byte <= byte_offset <= fn.end_byte:
            if best_fn is None or \
               (fn.end_byte - fn.start_byte) < (best_fn.end_byte - best_fn.start_byte):
                best_fn = fn
    if best_fn is not None:
        name_node = best_fn.child_by_field_name('name')
        if name_node:
            return node_to_text(name_node)
    return '<top-level>'

def _find_function_by_name(vs_parser, root_node, fn_name):
    """
    Find a function node in the AST by its name.
    Returns the function node or None.
    """
    functions = vs_parser.extract_function(root_node)
    for fn in functions:
        name_node = fn.child_by_field_name('name')
        if name_node and node_to_text(name_node) == fn_name:
            return fn
    return None

def _find_raw_line_range(cleaned_context_lines, raw_lines, raw_fn_node):
    """
    Given line(s) from the cleaned program that an AST diff node spans,
    find the corresponding line range in the raw program by matching
    stripped line content within the enclosing raw function's span.

    Args:
        cleaned_context_lines: list of lines from the cleaned program.
        raw_lines: all lines of the raw program.
        raw_fn_node: the enclosing function node in the raw AST, or None.

    Returns:
        (start_1based, end_1based) or None if not found.
    """
    if raw_fn_node is not None:
        search_start = raw_fn_node.start_point[0]
        search_end = raw_fn_node.end_point[0]
    else:
        search_start = 0
        search_end = len(raw_lines) - 1

    # Collect non-blank stripped lines as search targets
    targets = [l.strip() for l in cleaned_context_lines if l.strip()]
    if not targets:
        return None

    first_target = targets[0]
    last_target = targets[-1]

    # Find first target in raw lines
    start_raw = None
    for i in range(search_start, search_end + 1):
        if raw_lines[i].strip() == first_target:
            start_raw = i
            break
    if start_raw is None:
        return None

    if len(targets) == 1:
        return (start_raw + 1, start_raw + 1)

    # Find last target (searching forward from start_raw)
    end_raw = start_raw
    for i in range(start_raw + 1, search_end + 1):
        if raw_lines[i].strip() == last_target:
            end_raw = i
            break

    return (start_raw + 1, end_raw + 1)


def _format_git_diff(diffs, vs_parser,
                     cleaned_src_root, cleaned_dst_root,
                     cleaned_src_program, cleaned_dst_program,
                     raw_src_program, raw_dst_program,
                     raw_src_root, raw_dst_root):
    """
    Format collected AST diffs into a git-diff-style string.
    For each AST diff node:
      1. Extract the lines it spans in the cleaned program.
      2. Find the enclosing function name from the cleaned AST.
      3. Locate those lines in the raw program (by stripped content
         match within the enclosing raw function's span).
      4. Output those raw lines as a diff hunk.
    Hunks that map to the same raw line range are deduplicated.
    Each hunk header includes the enclosing function name.
    """
    if not diffs:
        return ''

    cleaned_src_lines = cleaned_src_program.split('\n')
    cleaned_dst_lines = cleaned_dst_program.split('\n')
    raw_src_lines = raw_src_program.split('\n')
    raw_dst_lines = raw_dst_program.split('\n')

    parts = ['--- a/src', '+++ b/dst']
    seen_hunks = set()  # deduplicate by (fn_name, src_range, dst_range)

    for diff_type, src_node, dst_node in diffs:
        if diff_type == 'modify':
            fn_name = _find_enclosing_function_name(
                vs_parser, cleaned_src_root, src_node.start_byte)

            # Lines this diff node spans in the cleaned programs
            src_context = cleaned_src_lines[
                src_node.start_point[0]:src_node.end_point[0] + 1]
            dst_context = cleaned_dst_lines[
                dst_node.start_point[0]:dst_node.end_point[0] + 1]

            raw_src_fn = _find_function_by_name(
                vs_parser, raw_src_root, fn_name)
            raw_dst_fn = _find_function_by_name(
                vs_parser, raw_dst_root, fn_name)

            src_range = _find_raw_line_range(
                src_context, raw_src_lines, raw_src_fn)
            dst_range = _find_raw_line_range(
                dst_context, raw_dst_lines, raw_dst_fn)
            if src_range is None or dst_range is None:
                continue

            hunk_key = (fn_name, src_range, dst_range)
            if hunk_key in seen_hunks:
                continue
            seen_hunks.add(hunk_key)

            src_start, src_end = src_range
            dst_start, dst_end = dst_range
            parts.append(
                f'@@ -{src_start},{src_end - src_start + 1}'
                f' +{dst_start},{dst_end - dst_start + 1} @@ {fn_name}')
            for line in raw_src_lines[src_start - 1:src_end]:
                parts.append(f'-{line}')
            for line in raw_dst_lines[dst_start - 1:dst_end]:
                parts.append(f'+{line}')

        elif diff_type == 'delete':
            fn_name = _find_enclosing_function_name(
                vs_parser, cleaned_src_root, src_node.start_byte)

            src_context = cleaned_src_lines[
                src_node.start_point[0]:src_node.end_point[0] + 1]
            raw_src_fn = _find_function_by_name(
                vs_parser, raw_src_root, fn_name)
            src_range = _find_raw_line_range(
                src_context, raw_src_lines, raw_src_fn)
            if src_range is None:
                continue

            hunk_key = (fn_name, src_range, None)
            if hunk_key in seen_hunks:
                continue
            seen_hunks.add(hunk_key)

            src_start, src_end = src_range
            parts.append(
                f'@@ -{src_start},{src_end - src_start + 1}'
                f' +0,0 @@ {fn_name}')
            for line in raw_src_lines[src_start - 1:src_end]:
                parts.append(f'-{line}')

        elif diff_type == 'insert':
            fn_name = _find_enclosing_function_name(
                vs_parser, cleaned_dst_root, dst_node.start_byte)

            dst_context = cleaned_dst_lines[
                dst_node.start_point[0]:dst_node.end_point[0] + 1]
            raw_dst_fn = _find_function_by_name(
                vs_parser, raw_dst_root, fn_name)
            dst_range = _find_raw_line_range(
                dst_context, raw_dst_lines, raw_dst_fn)
            if dst_range is None:
                continue

            hunk_key = (fn_name, None, dst_range)
            if hunk_key in seen_hunks:
                continue
            seen_hunks.add(hunk_key)

            dst_start, dst_end = dst_range
            parts.append(
                f'@@ -0,0'
                f' +{dst_start},{dst_end - dst_start + 1} @@ {fn_name}')
            for line in raw_dst_lines[dst_start - 1:dst_end]:
                parts.append(f'+{line}')

    return '\n'.join(parts)

def spec_compatible_diff(src_prog: str, dst_prog: str, language_path: str) -> tuple:
    """
    Compare two programs for spec compatibility (same logic as spec_compatible)
    and output the error locations in git diff format with the enclosing
    function name annotated on each hunk.

    Comparison logic:
      1. Remove proof and comments from both programs.
      2. Compute tree hashes bottom-to-top; drill into children to find
         the deepest (most specific) differing AST nodes.
      3. Format each difference as a git-diff hunk, annotated with the
         enclosing function/method name.

    Args:
        src_prog: source program text.
        dst_prog: destination program text.
        language_path: path to the tree-sitter language .so file.

    Returns:
        (is_compatible, diff_string):
            is_compatible  – True iff the specs are identical.
            diff_string    – git-diff-formatted string showing where the
                             specs diverge, with each hunk labelled by
                             the enclosing function name.
    """
    src_editor = verus_editor(src_prog, language_path)
    src_editor.remove_proof()
    src_editor.remove_comment()

    dst_editor = verus_editor(dst_prog, language_path)
    dst_editor.remove_proof()
    dst_editor.remove_comment()

    vs_parser = src_editor.vs_parser
    cleaned_src_root = src_editor.current_ast.root_node
    cleaned_dst_root = dst_editor.current_ast.root_node

    # Raw (original) programs and ASTs for output
    raw_src_root = src_editor.raw_ast.root_node
    raw_dst_root = dst_editor.raw_ast.root_node

    src_hash = vs_parser.get_tree_hash(cleaned_src_root)
    dst_hash = vs_parser.get_tree_hash(cleaned_dst_root)

    if src_hash == dst_hash:
        return True, ''

    diffs = []
    _collect_tree_diffs(vs_parser, cleaned_src_root, cleaned_dst_root, diffs)

    diff_str = _format_git_diff(
        diffs, vs_parser,
        cleaned_src_root, cleaned_dst_root,
        src_editor.current_program, dst_editor.current_program,
        src_editor.raw_program, dst_editor.raw_program,
        raw_src_root, raw_dst_root
    )

    return False, diff_str

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

def proof_fn_spec_compatible_diff(src_prog: str, dst_prog: str, language_path: str) -> tuple:
    '''
    Check if the proof function specifications in src_prog and dst_prog are
    compatible, and output the error
    locations in git diff format with the enclosing function name annotated
    on each hunk.

    Returns:
        (is_compatible, diff_string):
            is_compatible  – True iff the proof function specs are identical.
            diff_string    – git-diff-formatted string showing where the
                             proof function specs diverge, with each hunk
                             labelled by the proof function name.
    '''
    src_editor = verus_editor(src_prog, language_path)
    src_editor.remove_proof_with_body()
    src_editor.remove_comment()
    proof_function_names = []
    src_proof_fns = {}        # fn_name -> tree_hash
    src_proof_fn_nodes = {}   # fn_name -> AST node (in cleaned AST)
    for fn in src_editor.vs_parser.extract_proof_fn(src_editor.current_ast.root_node):
        remove_decreases(src_editor, fn.child_by_field_name('specifications'))
    for fn in src_editor.vs_parser.extract_proof_fn(src_editor.current_ast.root_node):
        fn_name = fn.child_by_field_name('name').text.decode()
        proof_function_names.append(fn_name)
        src_proof_fns[fn_name] = src_editor.vs_parser.get_tree_hash(fn)
        src_proof_fn_nodes[fn_name] = fn

    dst_editor = verus_editor(dst_prog, language_path)
    dst_editor.remove_proof_with_body()
    dst_editor.remove_comment()
    dst_proof_fns = {}
    dst_proof_fn_nodes = {}
    for fn in dst_editor.vs_parser.extract_proof_fn(dst_editor.current_ast.root_node):
        remove_decreases(dst_editor, fn.child_by_field_name('specifications'))
    for fn in dst_editor.vs_parser.extract_proof_fn(dst_editor.current_ast.root_node):
        fn_name = fn.child_by_field_name('name').text.decode()
        if fn_name in proof_function_names:
            dst_proof_fns[fn_name] = dst_editor.vs_parser.get_tree_hash(fn)
            dst_proof_fn_nodes[fn_name] = fn
        else:
            dst_editor.replace_nodes([fn], target_str='')

    is_compatible = (
        all(fn_name in dst_proof_fns for fn_name in src_proof_fns) and
        all(src_proof_fns[fn_name] == dst_proof_fns[fn_name]
            for fn_name in src_proof_fns)
    )

    if is_compatible:
        return True, ''

    # Collect AST diffs for each mismatched proof function
    vs_parser = src_editor.vs_parser
    raw_src_root = src_editor.raw_ast.root_node
    raw_dst_root = dst_editor.raw_ast.root_node

    all_diffs = []

    # Missing proof functions in dst
    for fn_name in src_proof_fns:
        if fn_name not in dst_proof_fns:
            all_diffs.append(('delete', src_proof_fn_nodes[fn_name], None))
            continue
        if src_proof_fns[fn_name] == dst_proof_fns[fn_name]:
            continue
        # Hash mismatch — drill into children to find specific diffs
        fn_diffs = []
        _collect_tree_diffs(
            vs_parser,
            src_proof_fn_nodes[fn_name],
            dst_proof_fn_nodes[fn_name],
            fn_diffs,
        )
        all_diffs.extend(fn_diffs)

    diff_str = _format_git_diff(
        all_diffs, vs_parser,
        src_editor.current_ast.root_node,
        dst_editor.current_ast.root_node,
        src_editor.current_program,
        dst_editor.current_program,
        src_editor.raw_program,
        dst_editor.raw_program,
        raw_src_root, raw_dst_root,
    )

    return False, diff_str

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
    with open('/home/chentianyu/LLaMA-Factory-Verus/static/cases/mbpp_0_src.rs', 'r') as f:
        src_prog = f.read()
    with open('/home/chentianyu/LLaMA-Factory-Verus/static/cases/mbpp_0_dst.rs', 'r') as f:
        dst_prog = f.read()
    res, diff = spec_compatible_diff(src_prog, dst_prog, '/home/chentianyu/verus.so')
    if not res:
        print(diff)

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
        result, diff = proof_fn_spec_compatible_diff(src_prog, dst_prog, '/home/v-nongyudi/verus.so')
        if not result:
            print(diff)
        print(f'Current result: {result}, ground truth: {result_gt}')
        assert result == result_gt, f"Test failed for input {input_idx}, prediction {pred_index}, expected {result_gt}, got {result}"
        print("Test passed!")

if __name__ == '__main__':
    # verified_storage_pipeline()
    # test_spec_compatible()
    test_case_spec_compatible()
    # test_case_proof_fn_spec_compatible()
    pass