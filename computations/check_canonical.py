#!/usr/bin/env python3
"""Canonical derivations (Lemma 2.3, Lemma 7.4 and Appendix C of the paper) by string rewriting. Python 3, standard
library only; a few seconds.

    python3 computations/check_canonical.py

The rule sequences below are those of the Lean definitions `canDeriv` (Statement.lean), `HTPDB.canDerivH`
(HTPDB/Defs.lean) and `RH.canDerivRH` (RH/Defs.lean); each rule is applied at its leftmost occurrence.
Letters: f, t (binary digits), 0, 1, 2 (ternary digits), / (left end of T and H), L (left end of R_H), . (right end).

1. T: for 2 <= n < 2^13, canDeriv(n) leads from can(n) = / bin'(n) . to can(T(n)); the derivations use all 11 rules,
   and the rule lists agree with `rulesST` of the Lean sources.
2. H: for the 6141 integers n in Dom(H) = {n >= 8 : n = 0 mod 4 or n = 7 mod 8} with n < 2^14 (and for n = 4),
   canDerivH(n) leads from can(n) to can(H(n)); the derivations use all 11 rules of H (= `HTPDB.rulesHT`); can(7) has
   no redex; outside the two classes no dynamic rule applies at the right end; H(n) >= 1 on Dom(H).
3. R_H: for the same 6141 integers, canDerivRH(n) leads from can_RH(n) = L t bin'(n) . = L bin(n) . to can_RH(H(n));
   the case n = 7 and the examples of the Lean sources; the derivations of all n < 2^14 in Dom(H) use exactly the ten
   used rules (`RH.usedRH`); L0 -> L and Lf -> L are not used in 300 derivations with random strategies; in each of
   the 2343 strings reachable from can_RH(n), 1 <= n < 200, by any strategy, the letter after L is t, 1 or 2.
4. Lemma 7.4: canDerivRH(n) is the image of canDerivH(n) under the lift, rule by rule (0 <= n < 2^14), and the
   numbers of uses compare as stated.

Prints ALL OK and exits with status 0 if every comparison succeeds; stops at the first failure with status 1.
"""
from __future__ import annotations

import random
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ARCTIC = Path(__file__).resolve().parent.parent / "CollatzProof" / "Arctic"


class CheckFailed(Exception):
    pass


def check(name: str, cond: bool, detail: str = "") -> None:
    if not cond:
        raise CheckFailed(f"{name}: comparison failed {detail}".rstrip())
    print(f"  [{name}] ok {detail}".rstrip())


# ---------------------------------------------------------------- reading rule lists from the Lean sources

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


def lean_rules(path: Path, name: str, left: str) -> list[tuple[str, str]]:
    letter = {"f": "f", "t": "t", "d0": "0", "d1": "1", "d2": "2", "lft": left, "rgt": "."}
    src = strip_lean_comments(path.read_text(encoding="utf-8"))
    m = re.search(r"\bdef\s+" + re.escape(name) + r"\b", src)
    if m is None:
        raise CheckFailed(f"definition {name} not found in {path.name}")
    j = src.index("[", src.index(":=", m.end()))
    depth, k = 0, j
    for k in range(j, len(src)):
        depth += (src[k] == "[") - (src[k] == "]")
        if depth == 0:
            break
    out = []
    for lhs, rhs in re.findall(r"⟨\[([^\]]*)\],\s*\[([^\]]*)\]⟩", src[j:k + 1]):
        out.append(tuple("".join(letter[x.strip().removeprefix("Letter.")] for x in s.split(",") if x.strip())
                         for s in (lhs, rhs)))
    return out


# ---------------------------------------------------------------- the maps and the canonical derivations

def T(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


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


def can(n):
    return "/" + binp(n) + "."


def can_rh(n):
    return "Lt" + binp(n) + "."


def tail_bits_lsb(y):
    """The digits of bin'(y), least significant first (`tailBitsLSB`)."""
    return [int(c) for c in reversed(bin(y)[3:])]


def a_rule(b, d):
    s = 3 * b + d
    return ("ft"[b] + str(d), str(s // 2) + "ft"[s % 2])


def left_rule(d):
    return {0: ("/0", "/t"), 1: ("/1", "/ff"), 2: ("/2", "/ft")}[d]


def left_rule_rh(d):
    return {0: ("L0", "L"), 1: ("L1", "Lt"), 2: ("L2", "Ltf")}[d]


def sweep(bits, d):
    out = []
    for b in bits:
        out.append(a_rule(b, d))
        d = (3 * b + d) // 2
    return out + [left_rule(d)]


def sweep_rh(bits, d):
    out = []
    for b in bits:
        out.append(a_rule(b, d))
        d = (3 * b + d) // 2
    return out + [a_rule(1, d), left_rule_rh((3 + d) // 2)]


FF, TTT = ("ff.", "0."), ("ttt.", "22.")


def can_deriv(n):
    if n % 2 == 0:
        return [("f.", ".")]
    return [("t.", "2.")] + sweep(tail_bits_lsb((n - 1) // 2), 2)


def can_deriv_h(n):
    if n % 4 == 0:
        return [FF] + sweep(tail_bits_lsb(n // 4), 0)
    if n % 8 == 7:
        m = (n - 7) // 8
        return [TTT] + sweep(tail_bits_lsb(m), 2) + sweep(tail_bits_lsb(3 * m + 2), 2)
    return []


def can_deriv_rh(n):
    if n % 4 == 0:
        return [FF] + sweep_rh(tail_bits_lsb(n // 4), 0)
    if n % 8 == 7:
        m = (n - 7) // 8
        return [TTT] + sweep_rh(tail_bits_lsb(m), 2) + sweep_rh(tail_bits_lsb(3 * m + 2), 2)
    return []


def lift(r):
    for d in range(3):
        if r == left_rule(d):
            return [a_rule(1, d), left_rule_rh((3 + d) // 2)]
    return [r]


def apply_seq(s, seq):
    """Apply the rules in order, each at its leftmost occurrence; None if a rule does not apply."""
    for l, r in seq:
        i = s.find(l)
        if i < 0:
            return None
        s = s[:i] + r + s[i + len(l):]
    return s


# ---------------------------------------------------------------- the checks

def part1():
    print("1. Canonical derivations of T")
    rules_st = lean_rules(ARCTIC / "Defs.lean", "rulesST", "/")
    bad, used = 0, set()
    for n in range(2, 1 << 13):
        seq = can_deriv(n)
        used |= set(seq)
        bad += apply_seq(can(n), seq) != can(T(n))
    check("can(n) ->* can(T(n)) along canDeriv(n)", bad == 0, "(2 <= n < 2^13)")
    check("the derivations use all 11 rules of rulesST", used == set(rules_st) and len(rules_st) == 11)


def part2():
    print("2. Canonical derivations of H")
    rules_ht = lean_rules(ARCTIC / "HTPDB" / "Defs.lean", "rulesHT", "/")
    cnt = bad = 0
    used = set()
    for n in range(1, 1 << 14):
        if in_dom(n):
            cnt += 1
            seq = can_deriv_h(n)
            used |= set(seq)
            bad += apply_seq(can(n), seq) != can(H(n))
    check("can(n) ->* can(H(n)) along canDerivH(n) for n in Dom(H), n < 2^14", bad == 0 and cnt == 6141,
          f"({cnt} integers)")
    check("also for n = 4", apply_seq(can(4), can_deriv_h(4)) == can(3))
    check("the derivations use all 11 rules of HTPDB.rulesHT", used == set(rules_ht) and len(rules_ht) == 11)
    check("can(7) = /tt. has no redex", not any(l in can(7) for l, _ in rules_ht))
    check("outside the classes 0 mod 4 and 7 mod 8 no dynamic rule applies at the right end",
          all(not can(n).endswith(("ff.", "ttt.")) for n in range(8, 4000) if not (n % 4 == 0 or n % 8 == 7)),
          "(8 <= n < 4000)")
    check("H(n) >= 1 on Dom(H)", all(H(n) >= 1 for n in range(8, 100000) if in_dom(n)), "(n < 10^5)")


def part3():
    print("3. Canonical derivations of R_H")
    rules_rh = lean_rules(ARCTIC / "RH" / "Defs.lean", "rulesRH", "L")
    used_rh = lean_rules(ARCTIC / "RH" / "Defs.lean", "usedRH", "L")
    unused = [("L0", "L"), ("Lf", "L")]
    check("rule lists: usedRH = rulesRH without L0 -> L and Lf -> L",
          len(rules_rh) == 12 and used_rh == [r for r in rules_rh if r not in unused])
    cnt = bad = 0
    for n in range(1, 1 << 14):
        if in_dom(n):
            cnt += 1
            bad += apply_seq(can_rh(n), can_deriv_rh(n)) != can_rh(H(n))
    check("can_RH(n) ->* can_RH(H(n)) along canDerivRH(n) for n in Dom(H), n < 2^14", bad == 0 and cnt == 6141,
          f"({cnt} integers)")
    check("also for n = 4", apply_seq(can_rh(4), can_deriv_rh(4)) == can_rh(3))
    check("n = 7: the formula of canDerivRH does not lead to can_RH(8) (here (n-7)/8 = 0)",
          apply_seq(can_rh(7), can_deriv_rh(7)) != can_rh(8))
    alt7 = [TTT, left_rule_rh(2)] + sweep_rh(tail_bits_lsb(2), 2)
    check("n = 7: another derivation (ttt. -> 22., L2 -> Ltf, then the second 2 crosses tf)",
          apply_seq(can_rh(7), alt7) == can_rh(8))
    check("the examples canDerivRH 12, 8, 15 of the Lean sources",
          can_deriv_rh(12) == [FF, a_rule(1, 0), a_rule(1, 1), left_rule_rh(2)]
          and can_deriv_rh(8) == [FF, a_rule(0, 0), a_rule(1, 0), left_rule_rh(1)]
          and can_deriv_rh(15) == [TTT, a_rule(1, 2), left_rule_rh(2), a_rule(1, 2), a_rule(0, 2), a_rule(1, 1),
                                   left_rule_rh(2)])
    check("can_RH(n) = L bin(n) .", all(can_rh(n) == "L" + bin(n)[2:].replace("0", "f").replace("1", "t") + "."
                                        for n in range(1, 5000)), "(1 <= n < 5000)")
    check("outside the two classes no dynamic rule applies at the right end",
          all(not can_rh(n).endswith(("ff.", "ttt.")) for n in range(1, 4000) if n % 8 in (1, 2, 3, 5, 6)))
    seen = {r for n in range(1, 1 << 14) if in_dom(n) for r in can_deriv_rh(n)}
    check("the derivations for n in Dom(H), n < 2^14, use exactly the ten rules of usedRH", seen == set(used_rh)
          and len(seen) == 10)
    check("for all n < 2^12 the rules of canDerivRH(n) are in usedRH",
          all(r in used_rh for n in range(1 << 12) for r in can_deriv_rh(n)))
    check("each of the ten rules occurs in canDerivRH 8, 12, 15 or 20",
          set(used_rh) == {r for n in (8, 12, 15, 20) for r in can_deriv_rh(n)})
    rng = random.Random(5)
    hit = 0
    for _ in range(300):
        s = "L" + bin(rng.randrange(8, 1 << 30))[2:].replace("0", "f").replace("1", "t") + "."
        for _ in range(4000):
            apps = [(i, l, r) for l, r in rules_rh for i in range(len(s)) if s.startswith(l, i)]
            if not apps:
                break
            i, l, r = rng.choice(apps)
            hit += (l, r) in unused
            s = s[:i] + r + s[i + len(l):]
    check("L0 -> L and Lf -> L are not used in derivations with random strategies", hit == 0,
          "(300 derivations of up to 4000 steps)")
    total, inv_ok, capped = 0, True, False
    for n in range(1, 200):
        start = can_rh(n)
        reach, stack = {start}, [start]
        while stack:
            s0 = stack.pop()
            inv_ok &= s0[1] in "t12"
            for l, r in rules_rh:
                i = s0.find(l)
                while i >= 0:
                    v = s0[:i] + r + s0[i + len(l):]
                    if v not in reach:
                        reach.add(v)
                        stack.append(v)
                    i = s0.find(l, i + 1)
            capped |= len(reach) > 20000
        total += len(reach)
    check("in every string reachable from can_RH(n), 1 <= n < 200, the letter after L is t, 1 or 2",
          inv_ok and not capped and total == 2343, f"({total} strings)")


def part4():
    print("4. R_H derivations are lifts of H derivations (Lemma 7.4)")
    bad = badc = 0
    for n in range(1 << 14):
        h, rh = can_deriv_h(n), can_deriv_rh(n)
        bad += [x for r in h for x in lift(r)] != rh
        badc += h.count(FF) != rh.count(FF) or h.count(TTT) != rh.count(TTT)
        badc += rh.count(left_rule_rh(1)) != h.count(left_rule(0))
        badc += rh.count(left_rule_rh(2)) != h.count(left_rule(1)) + h.count(left_rule(2))
        badc += any(rh.count(a_rule(b, d)) != h.count(a_rule(b, d)) + (h.count(left_rule(d)) if b == 1 else 0)
                    for b in range(2) for d in range(3))
    check("canDerivRH(n) = flatMap lift (canDerivH(n))", bad == 0, "(0 <= n < 2^14)")
    check("uses: ff., ttt. equal; L1 = /0; L2 = /1 + /2; t d = (t d in H) + (/d in H); f d equal", badc == 0)


def main():
    try:
        part1()
        part2()
        part3()
        part4()
    except CheckFailed as e:
        print(f"FAILED: {e}")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
