"""Print the tree-sitter-haskell parse tree of selected declarations (development aid for hs2lean).

    dump_tree.py FILE.lhs NAME [NAME ...]
"""
import sys
from hs2lean import parse_file, top_decls

def show(node, src, depth=0, out=sys.stdout):
    text = src[node.start_byte:node.end_byte].decode()
    label = (node.parent.field_name_for_child(
        [c.id for c in node.parent.children].index(node.id)) if node.parent else None)
    leaf = f'  "{text}"' if node.child_count == 0 or node.type in ("variable", "constructor", "integer", "string", "operator") else ""
    out.write(f'{"  " * depth}{(label + ": ") if label else ""}{node.type}{leaf}\n')
    if node.type not in ("variable", "constructor", "integer", "string", "operator"):
        for c in node.children:
            if c.is_named:
                show(c, src, depth + 1, out)

if __name__ == "__main__":
    src, root = parse_file(sys.argv[1])
    want = set(sys.argv[2:])
    for name, nodes in top_decls(src, root):
        if name in want:
            for n in nodes:
                show(n, src)
