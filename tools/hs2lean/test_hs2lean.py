"""Unit tests for hs2lean (run on the instance: ~/c0/venv/bin/python test_hs2lean.py)."""
from hs2lean import PARSER, Translator, DataInfo, Unsupported, top_decls


def expr(src_text):
    """Translate the body of `f = <expr>` and return the Lean text."""
    src = f"f = {src_text}\n".encode()
    root = PARSER.parse(src).root_node
    tr = Translator(src, DataInfo())
    (_, nodes), = list(top_decls(src, root))
    return tr.e(nodes[0].child_by_field_name("match").child_by_field_name("expression"), 2)


def check(hs, lean):
    got = expr(hs)
    assert got == lean, f"{hs!r}: expected {lean!r}, got {got!r}"
    print(f"ok  {hs:28} -> {got}")


def refuses(hs):
    try:
        expr(hs)
    except Unsupported as ex:
        print(f"ok  {hs:28} -> refused ({ex})")
        return
    raise AssertionError(f"{hs!r} should be refused")


# fixity: tree-sitter nests every chain to the right; we must re-associate
check("a - b + c", "(a - b) + c")          # infixl 6
check("a + b * c", "a + (b * c)")          # * binds tighter
check("a ++ b ++ c", "a ++ (b ++ c)")      # infixr 5
check("x .|. y .&. z", "x ||| (y &&& z)")  # .&. (7) tighter than .|. (5)
check("f a $ g $ h x", "f a (g (h x))")    # $ is infixr 0 application
check("a : b : []", "a :: (b :: [])")
check("a == b && c", "(a == b) && c")
refuses("a == b == c")                     # infix 4 non-associative: GHC rejects too
refuses("a <|> b")                         # unknown operator
print("all hs2lean tests passed")
