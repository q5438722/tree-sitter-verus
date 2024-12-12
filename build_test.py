from tree_sitter import Language, Parser

# Compile Tree-sitter language (ensure you have the correct .so file)
Language.build_library(
    '../verus.so',
    ['.']  # Replace with your grammar path
)
