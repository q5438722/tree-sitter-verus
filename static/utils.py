import os, sys
import json, jsonlines
import re

def load_jsonl(path):
    with jsonlines.open(path, 'r') as f:
        res = [item for item in f]
    return res

def dump_jsonl(data, filename):
    with jsonlines.open(filename, 'w') as f:
        for line in data:
            f.write(line)

def load_json(filename):
    with open(filename, 'r') as f:
        return json.load(f)

def dump_json(data, filename):
    with open(filename, 'w') as f:
        json.dump(data, f, indent=2)

def add_symbol(x):
    if x.strip() == '':
        return x
    return f"```rust\n{x}\n```"

def remove_symbol(text: str, idx: int = -1) -> str:
    try:
        code = re.findall(r"```rust(.*?)```", text, flags=re.DOTALL)[idx]
        return code
    except:
        return text

def load_js(path):
    assert path.endswith('.json') or path.endswith('.jsonl')
    
    if path.endswith('.json'):
        return load_json(path)
    else:
        return load_jsonl(path)

def get_first_rust_code(text: str) -> str:
    code = re.findall(r"```rust\n(.*?)```", text, flags=re.DOTALL)[0]
    return code

def node_to_text(node) -> str:
    return node.text.decode()
