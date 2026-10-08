#!/usr/bin/env python3
"""The three rewriting systems, their transcription and their dependency pair problems (Section 2.3, Table 3 and
Appendix C of the paper). Python 3, standard library only; about one second.

    python3 computations/check_systems.py [--tpdb DIR]

Letters: f, t (binary digits 0, 1), 0, 1, 2 (ternary digits), / (left end of T and H), L (left end of R_H), . (right
end). In Lean the left ends / and L are both the letter `lft`.

1. Transcription. The rules of the files collatz-T.ari and collatz-T-5or7mod8.ari of the directory
   SRS_Standard/Yolcu_21 of TPDB-ARI (https://github.com/TermCOMP/TPDB-ARI) at commit
   183f29db5ec7702215c6aabe12732bf3e836fced are written below verbatim (the lines `(rule ...)`, in the order of the
   files; the files themselves are not part of this release). They are parsed and compared, including the order, with
   the lists `rulesST` (Defs.lean) and `HTPDB.rulesHT` (HTPDB/Defs.lean) of the Lean sources. The rules of R_H are
   built from their description in Section 6 of the companion paper II and compared with `RH.rulesRH` and `RH.usedRH`
   (RH/Defs.lean), including the order. With `--tpdb DIR`, the files DIR/collatz-T.ari and DIR/collatz-T-5or7mod8.ari
   are also compared with the SHA-256 of the files at that commit and with the verbatim lines below.
2. Values. The carry and left-end rules preserve the value of a string, and the dynamic rules apply T and H.
3. Dependency pairs (Section 2.3). For T, H and their reversals: the dependency pairs (the defined symbols are the
   first letters of left-hand sides; a pair is marked at its first letter on both sides), an estimate of the
   dependency graph (TCAP: below the root, everything from the first defined symbol on is a fresh variable), its
   strongly connected components (SCCs), the subterm criterion, and the usable rules as the least closed set. They are
   compared with the statements of Section 2.3 and with the lists `pairsPB`, `usableST`, `pairsPDrev`, `usableSTrev`
   (DPStatement.lean) and `HTPDB.usableHT`, `HTPDB.pairsPDrevH`, `HTPDB.usableHTrev` (HTPDB/DPStatement.lean).
4. Root steps along canonical chains: the pairs of P_B are used at the root once per odd step of T, and once per step
   3n/4 and twice per step (9n+1)/8 of H; for T and 2 <= n <= 20000 the pairs /#0 -> /#t, /#1 -> /#ff, /#2 -> /#ft
   are used 4532, 2730 and 2737 times.

Prints ALL OK and exits with status 0 if every comparison succeeds; stops at the first failure with status 1.
"""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ARCTIC = Path(__file__).resolve().parent.parent / "CollatzProof" / "Arctic"

TPDB_COMMIT = "183f29db5ec7702215c6aabe12732bf3e836fced"
TPDB_SHA256 = {
    "collatz-T.ari": "db6638478684d0c7f4b7c4a9ae6a91d1286df26427734a1f8300a4d1b991ded8",
    "collatz-T-5or7mod8.ari": "d2c475a025ca32afcc60ba39e1b942f6da6c2c8a99bea5d208100a5d7153a526",
}
# The lines `(rule ...)` of SRS_Standard/Yolcu_21/collatz-T.ari at the commit above, verbatim and in order.
ARI_T = """\
(rule (b0 ($ x1)) ($ x1))
(rule (b1 ($ x1)) (t2 ($ x1)))
(rule (b0 (t0 x1)) (t0 (b0 x1)))
(rule (b0 (t1 x1)) (t0 (b1 x1)))
(rule (b0 (t2 x1)) (t1 (b0 x1)))
(rule (b1 (t0 x1)) (t1 (b1 x1)))
(rule (b1 (t1 x1)) (t2 (b0 x1)))
(rule (b1 (t2 x1)) (t2 (b1 x1)))
(rule (& (t0 x1)) (& (b1 x1)))
(rule (& (t1 x1)) (& (b0 (b0 x1))))
(rule (& (t2 x1)) (& (b0 (b1 x1))))
"""
# The lines `(rule ...)` of SRS_Standard/Yolcu_21/collatz-T-5or7mod8.ari at the commit above, verbatim and in order.
ARI_H = """\
(rule (b0 (b0 ($ x1))) (t0 ($ x1)))
(rule (b1 (b1 (b1 ($ x1)))) (t2 (t2 ($ x1))))
(rule (b0 (t0 x1)) (t0 (b0 x1)))
(rule (b0 (t1 x1)) (t0 (b1 x1)))
(rule (b0 (t2 x1)) (t1 (b0 x1)))
(rule (b1 (t0 x1)) (t1 (b1 x1)))
(rule (b1 (t1 x1)) (t2 (b0 x1)))
(rule (b1 (t2 x1)) (t2 (b1 x1)))
(rule (& (t0 x1)) (& (b1 x1)))
(rule (& (t1 x1)) (& (b0 (b0 x1))))
(rule (& (t2 x1)) (& (b0 (b1 x1))))
"""
ARI_LETTER = {"b0": "f", "b1": "t", "t0": "0", "t1": "1", "t2": "2", "&": "/", "$": "."}


class CheckFailed(Exception):
    pass


def check(name: str, cond: bool, detail: str = "") -> None:
    if not cond:
        raise CheckFailed(f"{name}: comparison failed {detail}".rstrip())
    print(f"  [{name}] ok {detail}".rstrip())


# ---------------------------------------------------------------- reading the ARI rules and the Lean sources

def parse_ari(text: str) -> list[tuple[str, str]]:
    """Rules `(rule lhs rhs)` between unary terms, read as string rules (outermost symbol first)."""
    rules = []
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("(rule"):
            continue
        body = line[len("(rule"):-1].strip()
        depth, cut = 0, None
        for i, ch in enumerate(body):
            depth += (ch == "(") - (ch == ")")
            if ch == ")" and depth == 0:
                cut = i + 1
                break
        lhs, rhs = body[:cut], body[cut:].strip()

        def word(term: str) -> str:
            toks = term.replace("(", " ").replace(")", " ").split()
            if toks[-1] != "x1":
                raise CheckFailed(f"unexpected term {term}")
            return "".join(ARI_LETTER[x] for x in toks[:-1])
        rules.append((word(lhs), word(rhs)))
    return rules


def strip_lean_comments(s: str) -> str:
    """Remove `--` line comments and nested block comments `/- -/` (string literals kept)."""
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth == 0 and s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append(s[i:j + 1])
            i = j + 1
            continue
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and s.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def lean_list(path: Path, name: str) -> str:
    """The outermost `[ ... ]` after `def <name> ... :=` in the Lean source (comments removed)."""
    src = strip_lean_comments(path.read_text(encoding="utf-8"))
    m = re.search(r"\bdef\s+" + re.escape(name) + r"\b", src)
    if m is None:
        raise CheckFailed(f"definition {name} not found in {path.name}")
    j = src.index("[", src.index(":=", m.end()))
    depth = 0
    for k in range(j, len(src)):
        depth += (src[k] == "[") - (src[k] == "]")
        if depth == 0:
            return src[j:k + 1]
    raise CheckFailed(f"unbalanced list {name}")


def lean_rules(path: Path, name: str, left: str = "/") -> list[tuple[str, str]]:
    """A Lean list of rules `⟨[...], [...]⟩` (letters `f t d0 d1 d2 lft rgt`, optionally `mark`/`plain`) as string
    rules; a marked letter is followed by '#'."""
    letter = {"f": "f", "t": "t", "d0": "0", "d1": "1", "d2": "2", "lft": left, "rgt": "."}
    out = []
    for lhs, rhs in re.findall(r"⟨\[([^\]]*)\],\s*\[([^\]]*)\]⟩", lean_list(path, name)):
        def word(s: str) -> str:
            res = ""
            for tok in (x.strip() for x in s.split(",")):
                if not tok:
                    continue
                parts = tok.split()
                if parts[0] in ("mark", "DLetter.mark"):
                    res += letter[parts[1].removeprefix("Letter.")] + "#"
                elif parts[0] in ("plain", "DLetter.plain"):
                    res += letter[parts[1].removeprefix("Letter.")]
                else:
                    res += letter[tok.removeprefix("Letter.")]
            return res
        out.append((word(lhs), word(rhs)))
    return out


# ---------------------------------------------------------------- the systems

A_RULES = [("f0", "0f"), ("f1", "0t"), ("f2", "1f"), ("t0", "1t"), ("t1", "2f"), ("t2", "2t")]
B_RULES = [("/0", "/t"), ("/1", "/ff"), ("/2", "/ft")]
D_T = [("f.", "."), ("t.", "2.")]
D_H = [("ff.", "0."), ("ttt.", "22.")]


def rules_RH_paper_ii() -> list[tuple[str, str]]:
    """R_H as described in Section 6 of paper II: the rules b d -> d' b' with 3b + d = 2d' + b' (b in {f, t} read
    as 0, 1; d in {0, 1, 2}), the left-end rules L0 -> L, L1 -> Lt, L2 -> Ltf, Lf -> L, and the dynamic rules
    ff. -> 0. and ttt. -> 22."""
    carry = []
    for b in (0, 1):
        for d in (0, 1, 2):
            s = 3 * b + d
            carry.append(("ft"[b] + str(d), str(s // 2) + "ft"[s % 2]))
    return carry + [("L0", "L"), ("L1", "Lt"), ("L2", "Ltf"), ("Lf", "L")] + D_H


def value(w: str) -> int:
    """Value of a string read from the left: / is the constant 1, L the constant 0, f: 2x, t: 2x+1, d: 3x+d."""
    v = 0
    for c in w:
        if c == "/":
            v = 1
        elif c == "L":
            v = 0
        elif c == "f":
            v = 2 * v
        elif c == "t":
            v = 2 * v + 1
        elif c in "012":
            v = 3 * v + int(c)
    return v


def T(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def H(n: int):
    if n % 4 == 0:
        return 3 * n // 4
    if n % 8 == 7:
        return (9 * n + 1) // 8
    return None


def binp(n: int) -> str:
    """bin'(n): the binary digits of n without the leading 1, written with f and t."""
    return "".join("f" if c == "0" else "t" for c in bin(n)[3:])


# ---------------------------------------------------------------- dependency pairs

def rev(R):
    return [(l[::-1], r[::-1]) for l, r in R]


def dps(R):
    """Dependency pairs of a string rewriting system (marks after the first letter of both sides)."""
    D = {l[0] for l, _ in R}
    P = []
    for l, r in R:
        for i in range(len(r)):
            if r[i] in D:
                P.append((l[0] + "#" + l[1:], r[i] + "#" + r[i + 1:]))
    return D, P


def edge(p, q, D) -> bool:
    """Estimated dependency graph: TCAP of the right-hand side of p unifies with the left-hand side of q."""
    t = p[1][2:]
    cut = next((i for i in range(len(t)) if t[i] in D), len(t))
    a, b = t[:cut], q[0][2:]
    m = min(len(a), len(b))
    return p[1][0] == q[0][0] and a[:m] == b[:m]


def sccs(n, adj):
    index, low, onst, st, out, c = {}, {}, set(), [], [], [0]

    def go(v):
        index[v] = low[v] = c[0]
        c[0] += 1
        st.append(v)
        onst.add(v)
        for w in adj[v]:
            if w not in index:
                go(w)
                low[v] = min(low[v], low[w])
            elif w in onst:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = st.pop()
                onst.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))
    for v in range(n):
        if v not in index:
            go(v)
    return out


def usable(R, pairs, D):
    """Usable rules: the least set containing the rules of the defined symbols below the root of the right-hand
    sides of the pairs and closed under the defined symbols of the right-hand sides of its rules."""
    need = set()
    for _, r in pairs:
        need |= {ch for ch in r[2:] if ch in D}
    U, changed = set(), True
    while changed:
        changed = False
        for l, r in R:
            if l[0] in need and (l, r) not in U:
                U.add((l, r))
                changed = True
                need |= {ch for ch in r if ch in D}
    return U


def subterm_criterion(pairs) -> bool:
    """The subterm criterion with the (only) projection to the argument of the unary marked root: every pair
    satisfies rhs-argument <= lhs-argument as subterms (a suffix of the lhs argument string), one strictly."""
    weak = all(l[2:].endswith(r[2:]) for l, r in pairs)
    strict = any(l[2:].endswith(r[2:]) and len(r) < len(l) for l, r in pairs)
    return weak and strict


def problem(R):
    D, P = dps(R)
    n = len(P)
    adj = [[j for j in range(n) if edge(P[i], P[j], D)] for i in range(n)]
    out = []
    for comp in sccs(n, adj):
        if len(comp) == 1 and comp[0] not in adj[comp[0]]:
            continue
        pairs = [P[i] for i in comp]
        out.append((sorted(pairs), usable(R, pairs, D), subterm_criterion(pairs)))
    return P, out


# ---------------------------------------------------------------- the checks

def part1(tpdb: Path | None) -> None:
    print("1. Transcription of the rules")
    ari_t, ari_h = parse_ari(ARI_T), parse_ari(ARI_H)
    lean_t = lean_rules(ARCTIC / "Defs.lean", "rulesST")
    lean_h = lean_rules(ARCTIC / "HTPDB" / "Defs.lean", "rulesHT")
    check("rulesST = rules of collatz-T.ari, in order", lean_t == ari_t, f"({len(lean_t)} rules)")
    check("HTPDB.rulesHT = rules of collatz-T-5or7mod8.ari, in order", lean_h == ari_h, f"({len(lean_h)} rules)")
    check("collatz-T = D_T, A, B in this order (Table 3)", ari_t == D_T + A_RULES + B_RULES)
    check("collatz-T-5or7mod8 = D_H, A, B in this order (Table 3)", ari_h == D_H + A_RULES + B_RULES)
    lean_rh = lean_rules(ARCTIC / "RH" / "Defs.lean", "rulesRH", left="L")
    used_rh = lean_rules(ARCTIC / "RH" / "Defs.lean", "usedRH", left="L")
    paper_ii = rules_RH_paper_ii()
    check("RH.rulesRH = rules of R_H in paper II, in order", lean_rh == paper_ii, f"({len(lean_rh)} rules)")
    check("RH.usedRH = rulesRH without L0 -> L and Lf -> L, in order",
          used_rh == [r for r in lean_rh if r not in (("L0", "L"), ("Lf", "L"))], f"({len(used_rh)} rules)")
    check("carry rules of R_H = those of T, dynamic rules of R_H = those of H",
          lean_rh[:6] == lean_t[2:8] and lean_rh[10:] == lean_h[:2])
    if tpdb is not None:
        for fn, verbatim in (("collatz-T.ari", ARI_T), ("collatz-T-5or7mod8.ari", ARI_H)):
            data = (tpdb / fn).read_bytes()
            check(f"{fn}: SHA-256 of the file at TPDB-ARI {TPDB_COMMIT[:12]}",
                  hashlib.sha256(data).hexdigest() == TPDB_SHA256[fn])
            lines = [ln.strip() for ln in data.decode("utf-8").splitlines() if ln.strip().startswith("(rule")]
            check(f"{fn}: rule lines = the verbatim lines of this script", lines == verbatim.splitlines())


def part2() -> None:
    print("2. Values")
    ctx = ["/", "/f", "/t", "/tf", "/ttf"]
    preserve = all(value(p + l + s) == value(p + r + s) for l, r in A_RULES for p in ctx for s in ("", "f", "t"))
    preserve &= all(value(l + s) == value(r + s) for l, r in B_RULES for s in ("", "f", "t", "tf"))
    check("A and B preserve the value (strings starting with /)", preserve)
    rh = rules_RH_paper_ii()
    ok = all(value(p + l + s) == value(p + r + s) for l, r in rh[:6] for p in ("L", "Lt", "Ltf") for s in ("", "t"))
    ok &= all(value(l + s) == value(r + s) for l, r in rh[6:10] for s in ("", "f", "t", "tf"))
    check("carry and left-end rules of R_H preserve the value (strings starting with L)", ok)
    dt = all(value("/" + binp(n)[:-1] + ("." if n % 2 == 0 else "2.")) == T(n) for n in range(2, 5000))
    check("D_T applies T: /bin'(n). -> /bin'(n)[:-1] + (. or 2.) has value T(n)", dt, "(2 <= n < 5000)")
    dh = True
    for n in range(8, 5000):
        if n % 4 == 0:
            dh &= value("/" + binp(n)[:-2] + "0.") == H(n)
        elif n % 8 == 7:
            dh &= value("/" + binp(n)[:-3] + "22.") == H(n)
    check("D_H applies H on the classes 0 mod 4 and 7 mod 8", dh, "(8 <= n < 5000)")


def part3() -> None:
    print("3. Dependency pairs, SCCs and usable rules (Section 2.3)")
    ST, HT = D_T + A_RULES + B_RULES, D_H + A_RULES + B_RULES
    PB = sorted([("/#0", "/#t"), ("/#1", "/#ff"), ("/#2", "/#ft")])
    A_set = set(A_RULES)
    res = {}
    for name, R in (("T", ST), ("H", HT), ("Trev", rev(ST)), ("Hrev", rev(HT))):
        P, comps = problem(R)
        res[name] = (P, comps)
        print(f"   {name}: {len(P)} dependency pairs, nontrivial SCCs of sizes {[len(c[0]) for c in comps]}")
    for name, D in (("T", D_T), ("H", D_H)):
        P, comps = res[name]
        check(f"{name}: 14 dependency pairs", len(P) == 14)
        root = sorted(p for p in P if p[1].startswith("/#"))
        check(f"{name}: the pairs with right-hand root /# are P_B, with left-hand root /#",
              root == PB and all(p[0].startswith("/#") for p in root))
        ess = [c for c in comps if c[0] == PB]
        check(f"{name}: P_B is an SCC with usable rules D u A (the unmarked left-end rules are not usable)",
              len(ess) == 1 and ess[0][1] == set(D) | A_set)
        carry = [c for c in comps if c[0] != PB]
        check(f"{name}: the other nontrivial SCC consists of 6 carry pairs, has no usable rules and is removed by the "
              "subterm criterion; P_B is not", len(carry) == 1 and len(carry[0][0]) == 6 and not carry[0][1]
              and carry[0][2] and not ess[0][2]
              and all(p[0][0] in "ft" and p[1][0] in "ft" for p in carry[0][0]))
        check(f"{name}: the remaining 5 pairs /#d -> f#... and /#d -> t#... lie in no SCC",
              sorted(set(P) - set(PB) - set(carry[0][0])) == sorted(p for p in P if p[0][0] == "/" and p[1][0] in "ft")
              and len(set(P) - set(PB) - set(carry[0][0])) == 5)
    ARev, BRev = set(rev(A_RULES)), set(rev(B_RULES))
    for name, n_pairs, ess_pairs in (("Trev", 9, sorted([(".#f", ".#"), (".#t", ".#2")])),
                                     ("Hrev", 11, sorted([(".#ff", ".#0"), (".#ttt", ".#22")]))):
        P, comps = res[name]
        check(f"{name}: {n_pairs} dependency pairs", len(P) == n_pairs)
        ess = [c for c in comps if c[0] == ess_pairs]
        check(f"{name}: the marked reversed dynamic rules form an SCC with usable rules A^rev u B^rev, not removed by "
              "the subterm criterion", len(ess) == 1 and ess[0][1] == ARev | BRev and not ess[0][2])
        carry = [c for c in comps if c[0] != ess_pairs]
        check(f"{name}: the other nontrivial SCC consists of carry pairs and is removed by the subterm criterion",
              len(carry) == 1 and carry[0][2] and all(p[0][0] in "012" for p in carry[0][0]))
    print("   comparison with the lists of the frozen statements")
    dp = ARCTIC / "DPStatement.lean"
    hdp = ARCTIC / "HTPDB" / "DPStatement.lean"
    st_lean = lean_rules(ARCTIC / "Defs.lean", "rulesST")
    check("pairsPB = P_B", sorted(lean_rules(dp, "pairsPB")) == PB)
    check("usableST = U(P_B) = first 8 rules of rulesST", set(lean_rules(dp, "usableST")) == set(D_T) | A_set
          and lean_rules(dp, "usableST") == st_lean[:8])
    pd_t = sorted([(".#f", ".#"), (".#t", ".#2")])
    pd_h = sorted([(".#ff", ".#0"), (".#ttt", ".#22")])
    check("pairsPDrev = P_T^rev", sorted(lean_rules(dp, "pairsPDrev")) == pd_t)
    check("usableSTrev = A^rev u B^rev", sorted(lean_rules(dp, "usableSTrev")) == sorted(ARev | BRev)
          and len(lean_rules(dp, "usableSTrev")) == 9)
    check("HTPDB.usableHT = U(P_B) for H", sorted(lean_rules(hdp, "usableHT")) == sorted(set(D_H) | A_set)
          and len(lean_rules(hdp, "usableHT")) == 8)
    check("HTPDB.pairsPDrevH = P_H^rev", sorted(lean_rules(hdp, "pairsPDrevH")) == pd_h)
    check("HTPDB.usableHTrev = A^rev u B^rev", sorted(lean_rules(hdp, "usableHTrev")) == sorted(ARev | BRev)
          and len(lean_rules(hdp, "usableHTrev")) == 9)
    # the lists computed here from the rules agree with the computed SCCs
    check("computed SCCs agree with these lists", [c for c in res["Trev"][1] if c[0] == pd_t][0][1] == ARev | BRev
          and [c for c in res["Hrev"][1] if c[0] == pd_h][0][1] == ARev | BRev)


LEFT = {0: [1], 1: [0, 0], 2: [0, 1]}


def root_digits(system: str, n: int):
    """Digits d arriving at the left end in the canonical derivation of n (each is one root step /#d -> /#...)."""
    bits = [int(c) for c in bin(n)[3:]]
    if system == "T":
        if bits[-1] == 0:
            return []
        digits, rest = [2], bits[:-1]
    else:
        if bits[-2:] == [0, 0]:
            digits, rest = [0], bits[:-2]
        elif bits[-3:] == [1, 1, 1]:
            digits, rest = [2, 2], bits[:-3]
        else:
            return None
    out = []
    for d in digits:
        j = len(rest)
        while j > 0:
            v = 3 * rest[j - 1] + d
            rest[j - 1], d = v % 2, v // 2
            j -= 1
        out.append(d)
        rest = LEFT[d] + rest
    return out


def part4() -> None:
    print("4. Root steps by pairs of P_B along canonical chains")
    cnt = {0: 0, 1: 0, 2: 0}
    ok_t = True
    for n in range(2, 20001):
        ds = root_digits("T", n)
        ok_t &= len(ds) == (1 if n % 2 else 0)
        for d in ds:
            cnt[d] += 1
    ok_h = True
    for n in range(16, 20001):
        ds = root_digits("H", n)
        if ds is not None:
            ok_h &= len(ds) == (1 if n % 4 == 0 else 2)
    check("T: one root step per odd step", ok_t, "(2 <= n <= 20000)")
    check("H: one root step per step 3n/4, two per step (9n+1)/8", ok_h, "(16 <= n <= 20000)")
    check("T: /#0, /#1, /#2 used 4532, 2730, 2737 times", (cnt[0], cnt[1], cnt[2]) == (4532, 2730, 2737),
          f"({cnt[0]}, {cnt[1]}, {cnt[2]})")


def main(argv: list[str]) -> int:
    tpdb = None
    if len(argv) == 2 and argv[0] == "--tpdb":
        tpdb = Path(argv[1])
    elif argv:
        print(__doc__.split("\n\n")[1])
        return 2
    try:
        part1(tpdb)
        part2()
        part3()
        part4()
    except CheckFailed as e:
        print(f"FAILED: {e}")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
