#!/usr/bin/env python3
"""The system R_H: the interpretation of Proposition 4.3, condition (CF), the subsystems of Proposition 4.5,
Lemma 5.2 for R_H, the left-end rules of R_H, and mutation tests (Appendix C of the paper). Python 3, standard
library only; a few seconds.

    python3 computations/check_rh.py

Letters: f, t, 0, 1, 2, L (left end), . (right end). Arctic matrices have entries in N u {-inf} (None is -inf).
[w] is the max-plus product of the matrices of the letters of w, from left to right.

1. The interpretation ILeft of dimension 2 (Proposition 4.3) agrees with its definition `RH.NonVacuityRH.ILeft` in
   RH/NonVacuity.lean; it weakly orients the 12 rules of R_H, strictly orients L0 -> L and Lf -> L and no used rule,
   has finite entries (M_s)_11, and does not satisfy (CF).
2. Subsystems (Proposition 4.5 for R_H): counting ternary digits weakly orients the first 10 rules and strictly
   orients L0 -> L, L1 -> Lt, L2 -> Ltf; counting binary digits weakly orients the used rules other than the two
   left-end rules and strictly orients the dynamic rules; every rule other than f0 -> 0f and t2 -> 2t is strictly
   oriented by counting some letter; L counted 3 and . counted 5 weakly orient all rules.
3. Lemma 5.2 for R_H: Phi(can_RH(n)) = ([L][t])_{1,*} (x) N_{bin'(n)} (x) ([.])_{*,1} for 300 random interpretations of
   dimensions 1 to 3 (10 integers each).
4. Left-end rules of R_H in the steps 3P/4 (8 <= P < 2^16, P = 0 mod 4): the leading digits 100 force L1 -> Lt and
   111 force L2 -> Ltf, and the left-end rule of R_H is L((3 + d)/2) for the digit d that reaches the left end in H.
5. Mutation tests: in a copy, the leading t of can_RH is dropped, the left-end rule for the digit 1 is replaced by
   L2 -> Ltf, the lift of /0 -> /t is changed, and one entry of ILeft is changed; each time some comparison fails.

Prints ALL OK and exits with status 0 if every comparison succeeds; stops at the first failure with status 1.
"""
from __future__ import annotations

import random
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ARCTIC = Path(__file__).resolve().parent.parent / "CollatzProof" / "Arctic"
NEG = None  # the arctic -inf


class CheckFailed(Exception):
    pass


def check(name: str, cond: bool, detail: str = "", quiet: bool = False) -> None:
    if not cond:
        raise CheckFailed(f"{name}: comparison failed {detail}".rstrip())
    if not quiet:
        print(f"  [{name}] ok {detail}".rstrip())


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
            if s[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def lean_ileft():
    """The cases `| Letter.x => !![a, b; c, d]` and `| _ => ...` of `def ILeft` in RH/NonVacuity.lean."""
    src = strip_lean_comments((ARCTIC / "RH" / "NonVacuity.lean").read_text(encoding="utf-8"))
    m = re.search(r"\bdef\s+ILeft\b", src)
    if m is None:
        raise CheckFailed("definition ILeft not found")
    blk = src[m.start():]
    blk = blk[:blk.index("\n\n")]

    def ent(e):
        e = e.strip()
        return NEG if e == "0" else int(e.removeprefix("Arc.fin "))
    cases = {}
    for pat, body in re.findall(r"\|\s*(Letter\.\w+|_)\s*=>\s*!!\[([^\]]*)\]", blk):
        cases[pat] = [[ent(e) for e in row.split(",")] for row in body.split(";")]
    name = {"f": "f", "t": "t", "0": "d0", "1": "d1", "2": "d2", "L": "lft", ".": "rgt"}
    return {c: cases.get("Letter." + name[c], cases["_"]) for c in "ft012L."}


# ---------------------------------------------------------------- R_H and its canonical derivations

def a_rule(b, d):
    s = 3 * b + d
    return ("ft"[b] + str(d), str(s // 2) + "ft"[s % 2])


CARRY = [a_rule(b, d) for b in range(2) for d in range(3)]
L0, LF = ("L0", "L"), ("Lf", "L")
FF, TTT = ("ff.", "0."), ("ttt.", "22.")
RULES = CARRY + [L0, ("L1", "Lt"), ("L2", "Ltf"), LF, FF, TTT]
USED = [r for r in RULES if r not in (L0, LF)]


def H(n):
    if n % 4 == 0:
        return 3 * n // 4
    if n % 8 == 7:
        return (9 * n + 1) // 8
    return None


def in_dom(n):
    return n >= 8 and (n % 4 == 0 or n % 8 == 7)


def binp(n):
    return "".join("f" if c == "0" else "t" for c in bin(n)[3:])


def tail_bits_lsb(y):
    return [int(c) for c in reversed(bin(y)[3:])]


def left_rule_h(d):
    return {0: ("/0", "/t"), 1: ("/1", "/ff"), 2: ("/2", "/ft")}[d]


# the interpretation ILeft of RH/NonVacuity.lean (compared with the Lean source in part 1)
ILEFT = {c: [[0, NEG], [0, NEG]] for c in "t12."}
ILEFT.update({"f": [[0, NEG], [1, 1]], "0": [[0, NEG], [1, 1]], "L": [[0, 0], [NEG, NEG]]})


class Model:
    """The definitions that the mutation tests alter."""

    def __init__(self):
        self.ileft = {c: [row[:] for row in m] for c, m in ILEFT.items()}

    def can_rh(self, n):
        return "Lt" + binp(n) + "."

    def left_rule_rh(self, d):
        return {0: L0, 1: ("L1", "Lt"), 2: ("L2", "Ltf")}[d]

    def sweep(self, bits, d, rh):
        out = []
        for b in bits:
            out.append(a_rule(b, d))
            d = (3 * b + d) // 2
        return out + ([a_rule(1, d), self.left_rule_rh((3 + d) // 2)] if rh else [left_rule_h(d)])

    def can_deriv(self, n, rh):
        if n % 4 == 0:
            return [FF] + self.sweep(tail_bits_lsb(n // 4), 0, rh)
        if n % 8 == 7:
            m = (n - 7) // 8
            return [TTT] + self.sweep(tail_bits_lsb(m), 2, rh) + self.sweep(tail_bits_lsb(3 * m + 2), 2, rh)
        return []

    def lift(self, r):
        for d in range(3):
            if r == left_rule_h(d):
                return [a_rule(1, d), self.left_rule_rh((3 + d) // 2)]
        return [r]


def apply_seq(s, seq):
    for l, r in seq:
        i = s.find(l)
        if i < 0:
            return None
        s = s[:i] + r + s[i + len(l):]
    return s


# ---------------------------------------------------------------- arctic matrices

def amul(A, B):
    n = len(A)
    C = [[NEG] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            vals = [A[i][k] + B[k][j] for k in range(n) if A[i][k] is not NEG and B[k][j] is not NEG]
            C[i][j] = max(vals) if vals else NEG
    return C


def ev(I, w):
    n = len(I["f"])
    M = [[0 if i == j else NEG for j in range(n)] for i in range(n)]
    for c in w:
        M = amul(M, I[c])
    return M


def le(a, b):
    return a is NEG or (b is not NEG and a <= b)


def weak(I, rule):
    l, r = ev(I, rule[0]), ev(I, rule[1])
    return all(le(r[i][j], l[i][j]) for i in range(len(l)) for j in range(len(l)))


def strict(I, rule):
    l, r = ev(I, rule[0]), ev(I, rule[1])
    return all((l[i][j] is NEG and r[i][j] is NEG) or (l[i][j] is not NEG and (r[i][j] is NEG or r[i][j] < l[i][j]))
               for i in range(len(l)) for j in range(len(l)))


def cf_holds(I):
    """(CF) for R_H: with S the set of indices reachable from the support of the first column of M_. along finite
    entries of M_f and M_t (s in S and (M_b)_{i,s} finite imply i in S), every column of M_f and M_t indexed by S has
    exactly one finite entry, and the first row of M_L is finite on S."""
    n = len(I["f"])
    reach = {j for j in range(n) if I["."][j][0] is not NEG}
    changed = True
    while changed:
        changed = False
        for b in "ft":
            for s in list(reach):
                for i in range(n):
                    if I[b][i][s] is not NEG and i not in reach:
                        reach.add(i)
                        changed = True
    cols = all(sum(I[b][i][j] is not NEG for i in range(n)) == 1 for b in "ft" for j in reach)
    return cols and all(I["L"][0][j] is not NEG for j in reach)


def count_interp(weights):
    """The one-dimensional interpretation counting letters with the given weights."""
    return {c: [[weights.get(c, 0)]] for c in "ft012L."}


# ---------------------------------------------------------------- the checks

def check_ileft(model, quiet=False):
    I = model.ileft
    check("ILeft = RH.NonVacuityRH.ILeft of the Lean source", lean_ileft() == I, quiet=quiet)
    check("ILeft weakly orients the 12 rules", all(weak(I, r) for r in RULES), quiet=quiet)
    check("ILeft strictly orients L0 -> L and Lf -> L", strict(I, L0) and strict(I, LF), quiet=quiet)
    check("ILeft strictly orients no used rule", not any(strict(I, r) for r in USED), quiet=quiet)
    check("all entries (M_s)_11 are finite", all(I[c][0][0] is not NEG for c in I), quiet=quiet)
    check("ILeft does not satisfy (CF) (the first column of M_f has two finite entries)", not cf_holds(I),
          quiet=quiet)


def check_canon(model, quiet=False):
    bad = sum(apply_seq(model.can_rh(n), model.can_deriv(n, True)) != model.can_rh(H(n))
              for n in range(8, 1 << 12) if in_dom(n))
    check("canonical derivations of R_H", bad == 0, "(n in Dom(H), n < 2^12)", quiet=quiet)


def check_lift(model, quiet=False):
    bad = badc = 0
    for n in range(1 << 12):
        h, rh = model.can_deriv(n, False), model.can_deriv(n, True)
        bad += [x for r in h for x in model.lift(r)] != rh
        badc += rh.count(model.left_rule_rh(1)) != h.count(left_rule_h(0))
        badc += rh.count(model.left_rule_rh(2)) != h.count(left_rule_h(1)) + h.count(left_rule_h(2))
    check("canDerivRH = lift of canDerivH, and the uses of L1 -> Lt and L2 -> Ltf", bad == 0 and badc == 0,
          "(n < 2^12)", quiet=quiet)


def part1():
    print("1. The interpretation ILeft (Proposition 4.3)")
    check_ileft(Model())


def part2():
    print("2. Subsystems and strict orientability (Proposition 4.5 for R_H)")
    wdig, wbit = count_interp({"0": 1, "1": 1, "2": 1}), count_interp({"f": 1, "t": 1})
    check("counting ternary digits: weak on the first 10 rules, strict on L0 -> L, L1 -> Lt, L2 -> Ltf",
          all(weak(wdig, r) for r in RULES[:10]) and all(strict(wdig, r) for r in (L0, ("L1", "Lt"), ("L2", "Ltf"))))
    da = CARRY + [FF, TTT]
    check("counting binary digits: weak on the carry and dynamic rules, strict on the dynamic rules",
          all(weak(wbit, r) for r in da) and strict(wbit, FF) and strict(wbit, TTT))
    poss = {r: [c for c in "ft012L." if strict(count_interp({c: 1}), r)] for r in RULES}
    check("every rule except f0 -> 0f and t2 -> 2t is strictly oriented by counting some letter",
          [r[0] for r in RULES if not poss[r]] == ["f0", "t2"])
    check("L counted 3 and . counted 5 weakly orient all 12 rules",
          all(weak(count_interp({"L": 3, ".": 5}), r) for r in RULES))


def part3():
    print("3. Lemma 5.2 for R_H on random interpretations")
    rng = random.Random(11)
    model = Model()
    bad = 0
    for _ in range(300):
        D = rng.randrange(1, 4)
        I = {c: [[(rng.randrange(4) if rng.random() < 0.7 else NEG) for _ in range(D)] for _ in range(D)]
             for c in "ft012L."}
        for c in I:
            I[c][0][0] = rng.randrange(4)
        Mlt = amul(I["L"], I["t"])
        for n in rng.sample(range(1, 3000), 10):
            N = ev(I, binp(n))
            vals = [Mlt[0][i] + N[i][j] + I["."][j][0] for i in range(D) for j in range(D)
                    if NEG not in (Mlt[0][i], N[i][j], I["."][j][0])]
            bad += (max(vals) if vals else NEG) != ev(I, model.can_rh(n))[0][0]
    check("Phi(can_RH(n)) = ([L][t])_{1,*} N_{bin'(n)} ([.])_{*,1}", bad == 0,
          "(300 interpretations of dimension 1 to 3)")


def part4():
    print("4. Left-end rules of R_H in the steps 3P/4")
    model = Model()
    bad = n100 = n111 = 0
    byd = [0, 0, 0]
    for P in range(8, 1 << 16, 4):
        rh = [r for r in model.can_deriv(P, True) if r[0].startswith("L")]
        top = bin(P)[2:5]
        n100 += top == "100"
        n111 += top == "111"
        bad += (top == "100" and rh != [model.left_rule_rh(1)]) or (top == "111" and rh != [model.left_rule_rh(2)])
        d = 3 * P // (1 << (P.bit_length() - 1)) - 3
        byd[d] += 1
        bad += rh != [model.left_rule_rh((3 + d) // 2)]
    check("leading digits 100 force L1 -> Lt, 111 force L2 -> Ltf; the rule is L((3+d)/2)",
          bad == 0 and (n100, n111) == (4096, 4095) and all(x > 0 for x in byd),
          f"({n100} and {n111} integers)")


class NoLeadingT(Model):
    def can_rh(self, n):
        return "L" + binp(n) + "."


class WrongLeft1(Model):
    def left_rule_rh(self, d):
        return super().left_rule_rh(2 if d == 1 else d)


class WrongLift(Model):
    def lift(self, r):
        if r == left_rule_h(0):
            return [a_rule(1, 0), self.left_rule_rh(2)]
        return super().lift(r)


class WrongEntry(Model):
    def __init__(self):
        super().__init__()
        self.ileft["0"][1][1] = 0


def fires(check_fn, model):
    try:
        check_fn(model, quiet=True)
    except CheckFailed:
        return True
    return False


def part5():
    print("5. Mutation tests")
    for check_fn in (check_ileft, check_canon, check_lift):
        check_fn(Model(), quiet=True)
    check("the unaltered definitions pass the three comparisons", True)
    check("dropping the leading t of can_RH is detected", fires(check_canon, NoLeadingT()))
    check("replacing the left-end rule for 1 by L2 -> Ltf is detected", fires(check_lift, WrongLeft1()))
    check("changing the lift of /0 -> /t is detected", fires(check_lift, WrongLift()))
    check("changing one entry of ILeft is detected", fires(check_ileft, WrongEntry()))


def main():
    try:
        part1()
        part2()
        part3()
        part4()
        part5()
    except CheckFailed as e:
        print(f"FAILED: {e}")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
