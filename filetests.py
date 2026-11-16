"""Tests for file input/output (il, mokil, jich ... tzibil / moktzibil) and programs from files (meyahil).
Every test runs in an empty temporary directory; expected values are computed in Python.
Usage: python3 filetests.py ../itzamna [../itzamna_asan]"""
import subprocess, sys, os, tempfile, shutil
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import reference as S

BINS = [os.path.abspath(b) for b in sys.argv[1:]] or [os.path.abspath("../itzamna")]
env = dict(os.environ, ASAN_OPTIONS="detect_leaks=0")

def M(x): return S.maya_number(F(x))
def LST(*xs): return "uhaj " + " mok ".join(xs) + " kal" if xs else "uhaj kal"
def codes(b):
    if isinstance(b, str): b = b.encode()
    return LST(*[M(c) for c in b])

tests = []      # (name, program, files before, expected output lines, files after (or None), expect error)
def T(name, prog, before=None, out=(), after=None, err=False):
    tests.append((name, prog, before or {}, list(out), after, err))

T("write then read", "jich beispiel tzibil Hello World kal\nwa s il beispiel kal\ntzib s kal mut",
  out=[codes("Hello World\n")], after={"beispiel.txt": b"Hello World\n"})
T("append lines and readlines",
  "jich a tzibil first kal\njich a moktzibil second line kal\njich a moktzibil third kal\nwa L mokil a kal\ntzib L kal mut",
  out=[LST(codes("first"), codes("second line"), codes("third"))],
  after={"a.txt": b"first\nsecond line\nthird\n"})
T("write a string value", "wa t wojol abc def kal\njich b tzibil t nup t kal mut", after={"b.txt": b"abc defabc def\n"})
T("wojol literal with calculation words", "jich c tzibil wojol the ka on kal mut", after={"c.txt": b"the ka on\n"})
T("literal without calculation words", "jich d tzibil Hello Welt kal mut", after={"d.txt": b"Hello Welt\n"})
T("calculation words without wojol are evaluated", "jich c tzibil the ka on kal mut", err=True)
T("overwrite", "jich e tzibil one kal\njich e tzibil two kal mut", after={"e.txt": b"two\n"})
T("empty write clears the file", "jich f tzibil wojol kal mut", before={"f.txt": b"old\n"}, after={"f.txt": b""})
T("append an empty line", "jich g moktzibil a kal\njich g moktzibil wojol kal\njich g moktzibil b kal mut", after={"g.txt": b"a\n\nb\n"})
T("append after a last line without newline", "jich h moktzibil y kal mut", before={"h.txt": b"x"}, after={"h.txt": b"x\ny\n"})
T("readlines edge cases (CRLF, blank line, no final newline)",
  "wa L mokil h kal\ntzib L kal mut", before={"h.txt": b"a\r\nb\n\nc"},
  out=[LST(codes("a"), codes("b"), codes(""), codes("c"))])
T("empty file", "wa L mokil i kal\ntzib L kal\nwa s il i kal\ntzib s kal mut", before={"i.txt": b""}, out=[LST(), LST()])
T("only newlines", "wa L mokil j kal tzib L kal mut", before={"j.txt": b"\n\n"}, out=[LST(codes(""), codes(""))])
T("copy roundtrip", "wa d il src kal\njich dst tzibil d kal mut", before={"src.txt": b"line one\nline two\n"},
  after={"dst.txt": b"line one\nline two\n", "src.txt": b"line one\nline two\n"})
T("utf-8 bytes", "wa s il u kal\ntzib s kal\njich v tzibil s kal mut", before={"u.txt": "Früchte\n".encode()},
  out=[codes("Früchte\n")], after={"v.txt": "Früchte\n".encode()})
T("missing file", "wa s il nothere kal mut", err=True)
T("keyword as file name", "wa s il ka kal mut", err=True)
T("write needs a string", "jich w tzibil ux kal mut", err=True, after={})
T("write rejects a byte above 255", "jich w tzibil uhaj la ajaw ux kal kal mut", err=True)
T("write rejects a nested list", "jich w tzibil uhaj uhaj jun kal kal kal mut", err=True)
T("bad jich form", "jich x kal mut", err=True)
T("filename must be a single word", "wa s il a b kal mut", before={"a.txt": b"x"}, err=True)

PROG = b"wa sq chokte x kaba x on x kal\nwa k kaba ho kal\ntzib sq pakal k kal kal\nmut\n"
T("meyahil: the name alone runs the file; functions and variables stay",
  "wa Inhalt meyahil prog kal\nInhalt\ntzib sq pakal ux kal kal\ntzib k kal mut",
  before={"prog.txt": PROG}, out=[M(25), M(9), M(5)])
T("meyahil does not run anything at definition", "wa Inhalt meyahil prog kal\ntzib wojol defined only kal mut",
  before={"prog.txt": PROG}, out=["defined only"])
T("meyahil: the code can run more than once", "wa Inhalt meyahil p2 kal\nInhalt mut Inhalt mut",
  before={"p2.txt": b"tzib wojol hello kal\n"}, out=["hello", "hello"])
T("meyahil: a code variable defined by the file", "wa Inhalt meyahil p3 kal\nInhalt mut\nHi mut",
  before={"p3.txt": b"wa Hi kaba tzib wojol hello kal kal\nHi\nmut\n"}, out=["hello", "hello"])
T("naming a string does not run it", "wa Inhalt il prog kal\nInhalt mut\ntzib wojol after kal mut",
  before={"prog.txt": PROG}, out=["after"])
T("meyahil inside a function: definitions stay in its scope",
  "wa Inhalt meyahil loc kal\nwa f chokte kaba Inhalt mut loc kal\ntzib f pakal kal kal\ntzib loc tzak jun kal mut",
  before={"loc.txt": b"wa loc kaba ho kal\n"}, out=[M(5)], err=True)
T("meyahil: a file that reads itself is caught", "wa Inhalt meyahil self kal Inhalt mut",
  before={"self.txt": b"wa Inhalt meyahil self kal\nInhalt\n"}, err=True)
T("meyahil: NUL byte", "wa s meyahil z kal mut", before={"z.txt": b"wa a kaba jun kal\x00\n"}, err=True)
T("meyahil: missing kal is found at definition", "wa s meyahil bad2 kal tzib wojol defined kal mut",
  before={"bad2.txt": b"wa x kaba jun\n"}, err=True)
T("meyahil: stray kal is found at definition", "wa s meyahil bad3 kal tzib wojol defined kal mut",
  before={"bad3.txt": b"tzib jun kal kal\n"}, err=True)
T("meyahil: text after wojol may contain keywords", "wa s meyahil w kal s mut",
  before={"w.txt": b"tzib wojol wa ek kim jich xok kal\n"}, out=["wa ek kim jich xok"])
T("meyahil: a runtime error inside the file", "wa s meyahil bad kal s mut", before={"bad.txt": b"tzib jun tzak kal\n"}, err=True)
T("meyahil: missing file", "wa s meyahil nothere kal mut", err=True)
T("meyahil: keyword as file name", "wa s meyahil ka kal mut", err=True)
T("meyahil: a code variable cannot be used in a calculation", "wa s meyahil prog kal tzib s tzak jun kal mut",
  before={"prog.txt": PROG}, err=True)
T("meyah is gone", "meyah x kal mut", err=True)
T("jel reads a number from a file", "wa t il n kal tzib t jel kal mut", before={"n.txt": b"pakal la tzak jun kal on ka\n"}, out=[M(22)])
T("jel on the lines of a file", "wa L mokil nums kal wa total kaba mih kal xok line tan L kabis wa total kaba total tzak line jel kal kal tzib total kal mut",
  before={"nums.txt": b"la on ho\nka\nla ajaw ka\n"}, out=[M(152)])
T("write a number as text into a file", "jich out tzibil pakal ho on la ajaw ka kal jel kal mut", after={"out.txt": (M(500) + "\n").encode()})
T("a compiler-like loop: count the lines of a file",
  "wa L mokil big kal\nwa n kaba mih kal\nxok line tan L kabis wa n kaba n tzak jun kal kal\ntzib n kal mut",
  before={"big.txt": b"".join(b"line %d\n" % i for i in range(250))}, out=[M(250)])

failed = 0
for binary in BINS:
    for name, prog, before, exp, after, err in tests:
        d = tempfile.mkdtemp()
        try:
            for fn, content in before.items():
                open(os.path.join(d, fn), "wb").write(content)
            open(os.path.join(d, "t.itz"), "w", encoding="utf-8").write(prog + "\n")
            try:
                p = subprocess.run([binary, "t.itz"], cwd=d, capture_output=True, text=True, env=env, timeout=120)
            except subprocess.TimeoutExpired:
                print(f"[{os.path.basename(binary)}] FAIL {name}: timeout"); failed += 1; continue
            got = [l[4:] for l in p.stdout.splitlines() if l.startswith(">>> ")]
            problems = []
            if got != exp: problems.append(f"output {got!r:.150} != {exp!r:.150}")
            if (p.returncode != 0) != err: problems.append(f"rc={p.returncode}, expected error={err}, stderr={p.stderr[:150]!r}")
            if "AddressSanitizer" in p.stderr: problems.append("ASan: " + p.stderr[:300])
            for fn, content in (after or {}).items():
                path = os.path.join(d, fn)
                actual = open(path, "rb").read() if os.path.exists(path) else None
                if actual != content: problems.append(f"file {fn}: {actual!r} != {content!r}")
            if after == {} and os.path.exists(os.path.join(d, "w.txt")): problems.append("w.txt must not be created")
            if problems:
                failed += 1
                print(f"[{os.path.basename(binary)}] FAIL {name}")
                for q in problems: print("   ", q)
        finally:
            shutil.rmtree(d)
print(f"{len(tests) * len(BINS)} test runs, {failed} failed")
