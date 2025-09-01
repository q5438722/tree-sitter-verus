import os, sys
import hashlib

import warnings
warnings.filterwarnings("ignore", category=FutureWarning)
import tree_sitter
from tree_sitter import Language, Parser


language = Language('../verus.so', 'rust')
parser = Parser()
parser.set_language(language)

with open('test_scripts/case1.rs', 'r') as f:
    code = f.read()
root_node = parser.parse(bytes(code, 'utf-8'))
print(root_node.root_node.children[2].children[0].children[2].children[2].children[-1].sexp())