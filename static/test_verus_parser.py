"""
Pytest test suite for verus_parser.

Tests parsing, extraction, editing, and spec-compatibility using example files
from the examples/ directory.
"""

import os
import sys
import pytest

# Ensure the static directory is on the path
sys.path.insert(0, os.path.dirname(__file__))

from verus_parser import verus_parser, verus_editor, spec_compatible
from utils import node_to_text

# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

LANGUAGE_PATH = os.environ.get(
    "VERUS_SO_PATH",
    os.path.join(os.path.expanduser("~"), "verus.so"),
)

EXAMPLES_DIR = os.path.join(os.path.dirname(__file__), "..", "examples")


def _read_example(name: str) -> str:
    with open(os.path.join(EXAMPLES_DIR, name), "r") as f:
        return f.read()


@pytest.fixture(scope="session")
def parser():
    """Session-scoped verus_parser instance."""
    return verus_parser(LANGUAGE_PATH)


@pytest.fixture(scope="session")
def mbpp_113_src():
    return _read_example("mbpp_113.rs")


@pytest.fixture(scope="session")
def mbpp_133_src():
    return _read_example("mbpp_133.rs")


@pytest.fixture(scope="session")
def mbpp_133_spec_src():
    return _read_example("mbpp_133_spec.rs")


@pytest.fixture(scope="session")
def verusfmt_src():
    return _read_example("verusfmt.rs")


@pytest.fixture(scope="session")
def bitmap_src():
    return _read_example("bitmap.rs")


@pytest.fixture(scope="session")
def raw_array_src():
    return _read_example("raw-array.rs")


@pytest.fixture(scope="session")
def weird_exprs_src():
    return _read_example("weird-exprs.rs")


@pytest.fixture(scope="session")
def ast_src():
    return _read_example("ast.rs")


def _parse(parser, src):
    """Parse source and return root node."""
    return parser.parser.parse(bytes(src, "utf-8")).root_node


# ===========================================================================
# 1. Parsing: every example file should parse without errors
# ===========================================================================

EXAMPLE_FILES = [
    f for f in os.listdir(EXAMPLES_DIR) if f.endswith(".rs")
]


@pytest.mark.parametrize("filename", sorted(EXAMPLE_FILES))
class TestParsing:
    """All example files must parse without syntax errors."""

    def test_parse_no_errors(self, parser, filename):
        src = _read_example(filename)
        root = _parse(parser, src)
        assert not root.has_error, f"{filename} has parse errors"

    def test_parse_root_type(self, parser, filename):
        src = _read_example(filename)
        root = _parse(parser, src)
        assert root.type == "source_file"


# ===========================================================================
# 2. Function extraction
# ===========================================================================

class TestExtractFunctions:
    def test_mbpp_113_total_functions(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        fns = parser.extract_functions(root)
        assert len(fns) == 4

    def test_mbpp_133_total_functions(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        fns = parser.extract_functions(root)
        assert len(fns) == 4

    def test_filter_by_spec_mode(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        spec_fns = parser.extract_functions(root, target_modes=["spec"])
        assert len(spec_fns) == 1
        assert "is_digit_sepc" in node_to_text(spec_fns[0])

    def test_filter_by_proof_mode(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        proof_fns = parser.extract_functions(root, target_modes=["proof"])
        assert len(proof_fns) == 1

    def test_skip_external(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        fns_all = parser.extract_functions(root, skip_external=False)
        fns_no_ext = parser.extract_functions(root, skip_external=True)
        # There is one function with external_body attributes
        assert len(fns_no_ext) < len(fns_all)

    def test_verusfmt_many_functions(self, parser, verusfmt_src):
        root = _parse(parser, verusfmt_src)
        fns = parser.extract_functions(root)
        assert len(fns) == 110

    def test_bitmap_functions(self, parser, bitmap_src):
        root = _parse(parser, bitmap_src)
        fns = parser.extract_functions(root)
        assert len(fns) == 11


# ===========================================================================
# 3. Comment extraction
# ===========================================================================

class TestExtractComments:
    def test_mbpp_113_comments(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        comments = parser.extract_comments(root)
        assert len(comments) == 3

    def test_bitmap_many_comments(self, parser, bitmap_src):
        root = _parse(parser, bitmap_src)
        comments = parser.extract_comments(root)
        assert len(comments) == 209

    def test_comments_sorted_by_position(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        comments = parser.extract_comments(root)
        for i in range(1, len(comments)):
            assert comments[i].start_byte >= comments[i - 1].start_byte


# ===========================================================================
# 4. Specification extraction
# ===========================================================================

class TestExtractSpecifications:
    def test_mbpp_113_specifications(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        specs = parser.extract_specifications(root)
        # 1 spec fn + 2 fn_qualifiers
        assert len(specs) == 3

    def test_mbpp_133_specifications(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        specs = parser.extract_specifications(root)
        assert len(specs) == 3

    def test_verusfmt_specifications(self, parser, verusfmt_src):
        root = _parse(parser, verusfmt_src)
        specs = parser.extract_specifications(root)
        assert len(specs) == 55

    def test_bitmap_specifications(self, parser, bitmap_src):
        root = _parse(parser, bitmap_src)
        specs = parser.extract_specifications(root)
        assert len(specs) == 10

    def test_weird_exprs_no_specs(self, parser, weird_exprs_src):
        root = _parse(parser, weird_exprs_src)
        specs = parser.extract_specifications(root)
        assert len(specs) == 0


# ===========================================================================
# 5. Proof extraction
# ===========================================================================

class TestExtractProofs:
    def test_mbpp_113_proofs(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        proofs = parser.extract_proofs(root)
        assert len(proofs) == 4

    def test_mbpp_133_proofs(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        proofs = parser.extract_proofs(root)
        assert len(proofs) == 5

    def test_bitmap_proofs(self, parser, bitmap_src):
        root = _parse(parser, bitmap_src)
        proofs = parser.extract_proofs(root)
        assert len(proofs) == 41

    def test_verusfmt_proofs(self, parser, verusfmt_src):
        root = _parse(parser, verusfmt_src)
        proofs = parser.extract_proofs(root)
        assert len(proofs) == 70

    def test_weird_exprs_proofs(self, parser, weird_exprs_src):
        root = _parse(parser, weird_exprs_src)
        proofs = parser.extract_proofs(root)
        assert len(proofs) == 7


# ===========================================================================
# 6. Loop annotation extraction
# ===========================================================================

class TestExtractLoopAnnotations:
    def test_mbpp_133_invariant(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        annots = parser.extract_loop_annotations(root)
        assert len(annots) == 1
        assert annots[0].type == "invariant_clause"

    def test_mbpp_113_invariant(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        annots = parser.extract_loop_annotations(root)
        assert len(annots) == 1
        assert annots[0].type == "invariant_clause"

    def test_filter_by_clause_type(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        annots = parser.extract_loop_annotations(root, target_clause=["ensures_clause"])
        assert len(annots) == 0  # mbpp_113 only has invariant_clause on loops


# ===========================================================================
# 7. Specific call extraction
# ===========================================================================

class TestExtractSpecificCalls:
    def test_reveal_calls(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        calls = parser.extract_specific_calls(root, prefixes=["reveal"])
        assert len(calls) == 1
        assert "reveal" in node_to_text(calls[0])

    def test_no_admit_calls(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        calls = parser.extract_specific_calls(root, prefixes=["admit"])
        assert len(calls) == 0


# ===========================================================================
# 8. External body extraction
# ===========================================================================

class TestExtractExternal:
    def test_mbpp_113_external(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        externals = parser.extract_external(root)
        assert len(externals) == 3

    def test_mbpp_133_external(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        externals = parser.extract_external(root)
        assert len(externals) == 4

    def test_raw_array_external(self, parser, raw_array_src):
        root = _parse(parser, raw_array_src)
        externals = parser.extract_external(root)
        assert len(externals) == 7


# ===========================================================================
# 9. Specific node extraction
# ===========================================================================

class TestExtractSpecificNodes:
    def test_fn_qualifier_nodes(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        qualifiers = parser.extract_specific_nodes(root, node_types=["fn_qualifier"])
        assert len(qualifiers) == 2

    def test_assert_expressions(self, parser, mbpp_133_src):
        root = _parse(parser, mbpp_133_src)
        asserts = parser.extract_specific_nodes(root, node_types=["assert_expression"])
        assert len(asserts) >= 1


# ===========================================================================
# 10. Tree hashing
# ===========================================================================

class TestTreeHash:
    def test_hash_deterministic(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        h1 = parser.get_tree_hash(root)
        h2 = parser.get_tree_hash(root)
        assert h1 == h2

    def test_hash_non_empty(self, parser, mbpp_113_src):
        root = _parse(parser, mbpp_113_src)
        h = parser.get_tree_hash(root)
        assert len(h) > 0

    def test_different_programs_different_hash(self, parser, mbpp_113_src, mbpp_133_src):
        r1 = _parse(parser, mbpp_113_src)
        r2 = _parse(parser, mbpp_133_src)
        assert parser.get_tree_hash(r1) != parser.get_tree_hash(r2)

    def test_same_program_same_hash(self, parser, mbpp_133_src, mbpp_133_spec_src):
        """mbpp_133 and mbpp_133_spec are identical files, so hashes should match."""
        r1 = _parse(parser, mbpp_133_src)
        r2 = _parse(parser, mbpp_133_spec_src)
        assert parser.get_tree_hash(r1) == parser.get_tree_hash(r2)


# ===========================================================================
# 11. verus_editor operations
# ===========================================================================

class TestVerusEditor:
    def test_remove_comment(self, mbpp_113_src):
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        editor.remove_comment()
        remaining = editor.vs_parser.extract_comments(editor.current_ast)
        assert len(remaining) == 0

    def test_remove_specification(self, mbpp_113_src):
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        editor.remove_specification()
        remaining = editor.vs_parser.extract_specifications(editor.current_ast)
        assert len(remaining) == 0

    def test_remove_proof(self, mbpp_113_src):
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        editor.remove_proof()
        remaining = editor.vs_parser.extract_proofs(editor.current_ast)
        assert len(remaining) == 0

    def test_remove_external(self, mbpp_113_src):
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        editor.remove_external()
        remaining = editor.vs_parser.extract_external(editor.current_ast)
        assert len(remaining) == 0

    def test_program_changes_after_edit(self, mbpp_113_src):
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        editor.remove_comment()
        assert editor.current_program != editor.raw_program

    def test_remove_proof_preserves_spec(self, mbpp_113_src):
        """Removing proofs should not remove spec functions."""
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        original_specs = editor.vs_parser.extract_specifications(editor.current_ast)
        editor.remove_proof()
        remaining_specs = editor.vs_parser.extract_specifications(editor.current_ast)
        # Spec functions should be preserved (fn_qualifiers may shift,
        # but spec fns themselves should remain)
        spec_fn_count_before = len(editor.vs_parser.extract_functions(
            _parse(editor.vs_parser, mbpp_113_src), target_modes=["spec"]))
        spec_fn_count_after = len(editor.vs_parser.extract_functions(
            editor.current_ast, target_modes=["spec"]))
        assert spec_fn_count_after == spec_fn_count_before

    def test_remove_comment_on_bitmap(self, bitmap_src):
        editor = verus_editor(bitmap_src, LANGUAGE_PATH)
        editor.remove_comment()
        remaining = editor.vs_parser.extract_comments(editor.current_ast)
        assert len(remaining) == 0

    def test_remove_proof_on_mbpp_133(self, mbpp_133_src):
        editor = verus_editor(mbpp_133_src, LANGUAGE_PATH)
        editor.remove_proof()
        remaining = editor.vs_parser.extract_proofs(editor.current_ast)
        assert len(remaining) == 0

    def test_current_program_valid_utf8(self, mbpp_113_src):
        """Edited program should remain valid UTF-8."""
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        editor.remove_proof()
        editor.remove_comment()
        # If this doesn't raise, the program is valid UTF-8
        editor.current_program.encode("utf-8")

    def test_current_ast_reparseable(self, mbpp_113_src):
        """After edits the AST should still parse without errors."""
        editor = verus_editor(mbpp_113_src, LANGUAGE_PATH)
        editor.remove_proof()
        assert not editor.current_ast.has_error


# ===========================================================================
# 12. spec_compatible — the core compatibility check
# ===========================================================================

class TestSpecCompatible:
    """
    spec_compatible strips proofs, comments, and external bodies, then
    compares tree hashes. Two programs are spec-compatible when they share
    the same specification surface.
    """

    # --- positive cases (should be compatible) ---

    def test_self_compatible_mbpp_113(self, mbpp_113_src):
        assert spec_compatible(mbpp_113_src, mbpp_113_src, LANGUAGE_PATH)

    def test_self_compatible_mbpp_133(self, mbpp_133_src):
        assert spec_compatible(mbpp_133_src, mbpp_133_src, LANGUAGE_PATH)

    def test_mbpp_133_vs_mbpp_133_spec(self, mbpp_133_src, mbpp_133_spec_src):
        """mbpp_133.rs and mbpp_133_spec.rs should be spec-compatible
        (same specs, possibly different proofs)."""
        assert spec_compatible(mbpp_133_src, mbpp_133_spec_src, LANGUAGE_PATH)

    def test_mbpp_133_spec_vs_mbpp_133(self, mbpp_133_src, mbpp_133_spec_src):
        """spec_compatible should be symmetric."""
        assert spec_compatible(mbpp_133_spec_src, mbpp_133_src, LANGUAGE_PATH)

    def test_self_compatible_bitmap(self, bitmap_src):
        assert spec_compatible(bitmap_src, bitmap_src, LANGUAGE_PATH)

    def test_self_compatible_verusfmt(self, verusfmt_src):
        assert spec_compatible(verusfmt_src, verusfmt_src, LANGUAGE_PATH)

    # --- negative cases (should NOT be compatible) ---

    def test_different_programs_incompatible(self, mbpp_113_src, mbpp_133_src):
        assert not spec_compatible(mbpp_113_src, mbpp_133_src, LANGUAGE_PATH)

    def test_incompatible_is_symmetric(self, mbpp_113_src, mbpp_133_src):
        assert not spec_compatible(mbpp_133_src, mbpp_113_src, LANGUAGE_PATH)

    def test_bitmap_vs_mbpp_113(self, bitmap_src, mbpp_113_src):
        assert not spec_compatible(bitmap_src, mbpp_113_src, LANGUAGE_PATH)

    # --- comment-only differences should be compatible ---

    def test_comment_difference_compatible(self, mbpp_113_src):
        """Adding a comment should not break spec compatibility."""
        modified = "// extra comment at the top\n" + mbpp_113_src
        assert spec_compatible(mbpp_113_src, modified, LANGUAGE_PATH)

    # --- proof-only differences should be compatible ---

    def test_proof_difference_compatible(self, mbpp_133_src):
        """
        Removing proofs from one copy should still be spec-compatible
        with the original, since spec_compatible strips proofs.
        """
        editor = verus_editor(mbpp_133_src, LANGUAGE_PATH)
        editor.remove_proof()
        stripped = editor.current_program
        assert spec_compatible(mbpp_133_src, stripped, LANGUAGE_PATH)


# ===========================================================================
# 13. Edge cases
# ===========================================================================

class TestEdgeCases:
    def test_empty_program(self, parser):
        root = _parse(parser, "")
        fns = parser.extract_functions(root)
        assert len(fns) == 0

    def test_minimal_function(self, parser):
        src = "fn foo() {}"
        root = _parse(parser, src)
        assert not root.has_error
        fns = parser.extract_functions(root)
        assert len(fns) == 1

    def test_verus_block(self, parser):
        src = "verus! { spec fn bar() -> bool { true } }"
        root = _parse(parser, src)
        assert not root.has_error
        fns = parser.extract_functions(root)
        assert len(fns) >= 1

    def test_empty_compatible_with_empty(self):
        assert spec_compatible("", "", LANGUAGE_PATH)

    def test_merge_brackets(self):
        editor = verus_editor("fn foo() {}", LANGUAGE_PATH)
        merged = editor.merge_brackets([(0, 5), (3, 10), (15, 20)])
        assert merged == [(0, 10), (15, 20)]

    def test_merge_brackets_no_overlap(self):
        editor = verus_editor("fn foo() {}", LANGUAGE_PATH)
        merged = editor.merge_brackets([(0, 3), (5, 8), (10, 12)])
        assert merged == [(0, 3), (5, 8), (10, 12)]

    def test_merge_brackets_full_overlap(self):
        editor = verus_editor("fn foo() {}", LANGUAGE_PATH)
        merged = editor.merge_brackets([(0, 20), (5, 10)])
        assert merged == [(0, 20)]

    def test_ast_rs_pure_rust_no_specs(self, parser, ast_src):
        """ast.rs is pure Rust with no Verus specs."""
        root = _parse(parser, ast_src)
        specs = parser.extract_specifications(root)
        assert len(specs) == 0

    def test_weird_exprs_no_specs(self, parser, weird_exprs_src):
        """weird-exprs.rs is tricky Rust but has no Verus specs."""
        root = _parse(parser, weird_exprs_src)
        specs = parser.extract_specifications(root)
        assert len(specs) == 0
