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
check("(! r)", "(fun x => x r)")              # array index section (arrays are functions)
check("(// [(r, v)])", "(fun x => arrayUpdH x ([(r, v)]))")
refuses("a == b == c")                     # infix 4 non-associative: GHC rejects too
refuses("a <|> b")                         # unknown operator


def fun(src_text, name):
    src = src_text.encode()
    root = PARSER.parse(src).root_node
    tr = Translator(src, DataInfo())
    nodes = dict(top_decls(src, root))[name]
    return tr.emit_function(name, nodes)


# guards (regression: guards were once silently dropped, keeping only the first branch)
g = fun("h :: Int -> Int\nh x | x > 0 = 1\n    | otherwise = 2\n", "h")
assert "if (x > 0) then" in g and "else" in g and "2" in g, g
print("ok  guarded equation -> if/else")
g = fun("f :: Int -> Int\nf x = g x\n  where g a | a == 0 = 1\n            | otherwise = a\n", "f")
assert "if (a == 0) then" in g, g
print("ok  guarded where-function -> if/else")
g = fun("k :: Int -> Int\nk x | x > 0 = 1\n", "k")
assert "default" in g, g
print("ok  guards without otherwise (last equation) -> default")
try:
    fun("m :: Int -> Int\nm 0 | False = 1\nm x = x\n", "m")
    raise AssertionError("fall-through guards should be refused")
except Unsupported as ex:
    print(f"ok  guards falling through to the next equation -> refused")
# scoping (regression: a local variable named like a record field was turned into the selector)
def fun_with_data(src_text, name, data_src):
    from hs2lean import DataInfo as DI
    src = (data_src + "\n" + src_text).encode()
    root = PARSER.parse(src).root_node
    data = DI()
    tr = Translator(src, data)
    decls = dict(top_decls(src, root))
    for dn, dnodes in decls.items():
        if dnodes[0].type == "data_type":
            tr.collect_data(dn, dnodes[0])
    tr.bound = {"len"}
    return tr.emit_function(name, decls[name])
g = fun_with_data("f :: Int -> Int\nf len = len + 1\n", "f", "data R = R { len :: Int }")
assert "R.len" not in g and "len + 1" in g, g
print("ok  bound variable shadows a record selector of the same name")
print("all hs2lean tests passed")
