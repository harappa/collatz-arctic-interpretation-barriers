#!/usr/bin/env python3
"""Positive growth without strict orientation: Example 4.7 (arctic) and its natural-number version, Proposition 9.5
and the remark after it in Section 9 of the paper. Python 3, standard library only; a few seconds.

    python3 computations/check_mod3.py

Letters: f, t (binary digits 0, 1), 0, 1, 2 (ternary digits), / (left end; L for R_H), . (right end).
Indices are numbered from 0 here: index 0 is the slow path and index 1 + r stands for the residue r modulo 3 of the
value read so far (the paper numbers them 1 and 2 + r).

Part A (Example 4.7). The arctic interpretation of dimension 4 with finite entries
   (M_b)_00 = 0, (M_b)_{1+r, 1+((2r+b) mod 3)} = 1, (M_d)_00 = 0, (M_d)_{1+r, 1+d} = 2,
   (M_/)_00 = (M_/)_02 = 0, (M_.)_00 = (M_.)_10 = 0.
 A1. It weakly orients the 11 rules of T, strictly orients none, and has finite entries (M_s)_00.
 A2. Phi(can(n)) = (l(n) - 1) [3 | n] and Phi(can(T(n))) <= Phi(can(n)) for 2 <= n < 20000.
 A3. The digit automaton: its strongly connected components relevant for can(n) are {0} (growth rate 0) and
     {1, 2, 3}, where M_f and M_t restrict to permutation matrices of weight 1, so every product of length k has
     exactly one finite entry k in each row (checked for all words of length at most 10): the component of maximal
     growth rate is the permutation block of growth rate 1. Its semigroup contains no matrix with all entries finite,
     and the interpretation does not satisfy (CF). The block is entered from the left end at the residue 1 and left at
     the residue 0.
Part B (Proposition 9.5, natural-number affine interpretations [s](y) = M_s y + v_s, Phi(w) = ([w](0))_0). Dimension 4,
   (M_b)_00 = 1, (M_b)_{1+r, 1+((2r+b) mod 3)} = 2, (M_d)_00 = 1, (M_d)_{1+r, 1+d} = 4, (M_/)_00 = (M_/)_{0, 1+r_in} = 1,
   (M_.)_00 = 1, v_. = e_0 + e_{1+r_out}, all other entries and vectors 0; r_in = 1 for T and H, 0 for R_H;
   r_out = 0 for T, 1 for H and R_H.
 B1. For T, H (11 rules each) and R_H (12 rules) it weakly orients all rules (matrices and vectors entrywise >=),
     strictly orients none (the first components of the vectors agree), and (M_s)_00 = 1 for every s.
 B2. Phi(can(n)) = 1 + 2^(l(n)-1) [n = r_out mod 3] for T and H, Phi(can_RH(n)) = 1 + 2^l(n) [n = 1 mod 3] for R_H,
     and the values do not increase along T and H (2 <= n < 2^14).
 B3. The residue indices form a component on which M_f and M_t are twice permutation matrices; they generate the six
     permutations (no positive matrix, so (P) fails); every product of length k is 2^k times a permutation matrix
     (all words of length at most 8); the component is relevant (it is entered from the left end and reaches the
     right end) for T, H and R_H.
 B4. (The remark after Proposition 9.5.) With start and end vectors e_0 + e_1, reading all binary digits including
     the leading one, the same digit matrices give phi(n) = 1 + 2^l(n) [3 | n], which does not increase along T
     (2 <= n < 2^14).
The Lean theorems paper_prop_9_5_T, paper_prop_9_5_H, paper_prop_9_5_RH and paper_prop_9_5_remark prove Part B
for all n; this program checks it independently, on finite ranges.

Prints ALL OK and exits with status 0 if every comparison succeeds; stops at the first failure with status 1.
"""
from __future__ import annotations

import itertools
import sys

sys.dont_write_bytecode = True
D = 4
NEG = None  # the arctic -inf


class CheckFailed(Exception):
    pass


def check(name: str, cond: bool, detail: str = "") -> None:
    if not cond:
        raise CheckFailed(f"{name}: comparison failed {detail}".rstrip())
    print(f"  [{name}] ok {detail}".rstrip())


A_RULES = [("f0", "0f"), ("f1", "0t"), ("f2", "1f"), ("t0", "1t"), ("t1", "2f"), ("t2", "2t")]
LEFT = [("/0", "/t"), ("/1", "/ff"), ("/2", "/ft")]
SYSTEMS = {
    "T": [("f.", "."), ("t.", "2.")] + A_RULES + LEFT,
    "H": [("ff.", "0."), ("ttt.", "22.")] + A_RULES + LEFT,
    "R_H": [("ff.", "0."), ("ttt.", "22.")] + A_RULES + [("/0", "/"), ("/1", "/t"), ("/2", "/tf"), ("/f", "/")],
}


def T(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def H(n):
    if n % 4 == 0:
        return 3 * n // 4
    if n % 8 == 7:
        return (9 * n + 1) // 8
    return None


def can_word(n, read_leading=False):
    digits = bin(n)[2:] if read_leading else bin(n)[3:]
    return "/" + "".join("ft"[int(c)] for c in digits) + "."


# ---------------------------------------------------------------- part A: the arctic interpretation

def amul(X, Y):
    n = len(X)
    out = [[NEG] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            vals = [X[i][k] + Y[k][j] for k in range(n) if X[i][k] is not NEG and Y[k][j] is not NEG]
            out[i][j] = max(vals) if vals else NEG
    return out


def arctic_interp():
    def mat(entries):
        M = [[NEG] * D for _ in range(D)]
        for (i, j), w in entries.items():
            M[i][j] = w
        return M
    I = {}
    for b, c in ((0, "f"), (1, "t")):
        I[c] = mat({(0, 0): 0, **{(1 + r, 1 + (2 * r + b) % 3): 1 for r in range(3)}})
    for d in range(3):
        I[str(d)] = mat({(0, 0): 0, **{(1 + r, 1 + d): 2 for r in range(3)}})
    I["/"] = mat({(0, 0): 0, (0, 2): 0})
    I["."] = mat({(0, 0): 0, (1, 0): 0})
    return I


def aev(I, w):
    M = I[w[0]]
    for c in w[1:]:
        M = amul(M, I[c])
    return M


def a_weak(I, rule):
    l, r = aev(I, rule[0]), aev(I, rule[1])
    return all(r[i][j] is NEG or (l[i][j] is not NEG and l[i][j] >= r[i][j]) for i in range(D) for j in range(D))


def a_strict(I, rule):
    l, r = aev(I, rule[0]), aev(I, rule[1])
    return all((l[i][j] is NEG and r[i][j] is NEG) or (l[i][j] is not NEG and (r[i][j] is NEG or l[i][j] > r[i][j]))
               for i in range(D) for j in range(D))


def components(N0, N1):
    adj = {i: {j for j in range(D) if N0[i][j] is not NEG or N1[i][j] is not NEG} for i in range(D)}

    def reach(i):
        seen, st = {i}, [i]
        while st:
            a = st.pop()
            for b in adj[a]:
                if b not in seen:
                    seen.add(b)
                    st.append(b)
        return seen
    R = {i: reach(i) for i in range(D)}
    comps = []
    for i in range(D):
        C = frozenset(j for j in range(D) if j in R[i] and i in R[j])
        if C not in comps:
            comps.append(C)
    return comps, R


def part_a():
    print("A1. Orientation of the 11 rules of T")
    I = arctic_interp()
    rules = SYSTEMS["T"]
    check("weakly orients all 11 rules", all(a_weak(I, r) for r in rules))
    check("strictly orients none", not any(a_strict(I, r) for r in rules))
    check("all (M_s)_00 are finite", all(I[c][0][0] is not NEG for c in I))
    print("A2. Values on canonical strings")
    def phi(n):
        """([can(n)])_00, computed as the first row of [/] times the digit matrices times the first column of [.]."""
        w = can_word(n)
        row = I[w[0]][0][:]
        for c in w[1:]:
            M = I[c]
            row = [max((row[k] + M[k][j] for k in range(D) if row[k] is not NEG and M[k][j] is not NEG),
                       default=NEG) for j in range(D)]
        return row[0]
    check("Phi(can(n)) = (l(n) - 1) [3 | n]", all(phi(n) == (n.bit_length() - 1) * (n % 3 == 0)
                                                 for n in range(2, 20000)), "(2 <= n < 20000)")
    check("Phi(can(T(n))) <= Phi(can(n))", all(phi(T(n)) <= phi(n) for n in range(2, 20000)), "(2 <= n < 20000)")
    print("A3. Components of the digit automaton")
    N0, N1 = I["f"], I["t"]
    comps, R = components(N0, N1)
    start = {j for j in range(D) if I["/"][0][j] is not NEG}
    end = {i for i in range(D) if I["."][i][0] is not NEG}
    check("entry from the left end at the slow path and the residue 1, exit at the slow path and the residue 0",
          start == {0, 2} and end == {0, 1})
    relevant = sorted((sorted(C) for C in comps if any(C & R[i] for i in start)
                       and any(j in end for c in C for j in R[c])), key=len)
    check("relevant components {0} and {1, 2, 3}", relevant == [[0], [1, 2, 3]])
    check("component {0}: (M_f)_00 = (M_t)_00 = 0, growth rate 0", N0[0][0] == 0 and N1[0][0] == 0)
    blk = [1, 2, 3]
    gens = [[[M[i][j] for j in blk] for i in blk] for M in (N0, N1)]
    perm1 = all(sorted(x for x in row if x is not NEG) == [1] for g in gens for row in g) and \
        all(sum(g[i][j] is not NEG for i in range(3)) == 1 for g in gens for j in range(3))
    check("on {1, 2, 3}, M_f and M_t are permutation matrices with weight 1", perm1)
    rows_ok = True
    for k in range(1, 11):
        for w in itertools.product((0, 1), repeat=k):
            M = gens[w[0]]
            for b in w[1:]:
                M = amul(M, gens[b])
            rows_ok &= all(sorted(x for x in row if x is not NEG) == [k] for row in M)
    check("every product of length k has exactly one finite entry k in each row (growth rate 1)", rows_ok,
          "(all words of length <= 10)")
    pat = lambda M: tuple(tuple(x is not NEG for x in row) for row in M)  # noqa: E731
    seen, frontier = {pat(g) for g in gens}, [pat(g) for g in gens]
    while frontier:
        P = frontier.pop()
        for g in gens:
            Q = tuple(tuple(any(P[i][k] and pat(g)[k][j] for k in range(3)) for j in range(3)) for i in range(3))
            if Q not in seen:
                seen.add(Q)
                frontier.append(Q)
    check("the semigroup of {1, 2, 3} contains no matrix with all entries finite (no (P-infinity))",
          not any(all(all(row) for row in P) for P in seen), f"({len(seen)} support patterns)")
    reach = set(end)
    changed = True
    while changed:
        changed = False
        for N in (N0, N1):
            for j in list(reach):
                for i in range(D):
                    if N[i][j] is not NEG and i not in reach:
                        reach.add(i)
                        changed = True
    cols = all(sum(N[i][j] is not NEG for i in range(D)) == 1 for N in (N0, N1) for j in reach)
    cf = cols and start >= reach
    check("(CF) does not hold", not cf)


# ---------------------------------------------------------------- part B: natural-number affine interpretations

ENTRY = {"T": 1, "H": 1, "R_H": 0}
EXIT = {"T": 0, "H": 1, "R_H": 1}


def nat_interp(system):
    def zero():
        return [[0] * D for _ in range(D)]
    I = {}
    for b, c in ((0, "f"), (1, "t")):
        M = zero()
        M[0][0] = 1
        for r in range(3):
            M[1 + r][1 + (2 * r + b) % 3] = 2
        I[c] = (M, [0] * D)
    for d in range(3):
        M = zero()
        M[0][0] = 1
        for r in range(3):
            M[1 + r][1 + d] = 4
        I[str(d)] = (M, [0] * D)
    M = zero()
    M[0][0] = 1
    M[0][1 + ENTRY[system]] = 1
    I["/"] = (M, [0] * D)
    M = zero()
    M[0][0] = 1
    v = [0] * D
    v[0] = 1
    v[1 + EXIT[system]] = 1
    I["."] = (M, v)
    return I


def nmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(D)) for j in range(D)] for i in range(D)]


def compose(I, word):
    """[s_1 ... s_k](y) = M y + v, with s_1 outermost."""
    M = [[int(i == j) for j in range(D)] for i in range(D)]
    v = [0] * D
    for s in word:
        Ms, vs = I[s]
        v = [v[i] + sum(M[i][k] * vs[k] for k in range(D)) for i in range(D)]
        M = nmul(M, Ms)
    return M, v


def value(I, word):
    """([word](0))_0, computed from the right: y = M_s y + v_s for the letters s from the last to the first."""
    y = [0] * D
    for s in reversed(word):
        Ms, vs = I[s]
        y = [sum(Ms[i][k] * y[k] for k in range(D)) + vs[i] for i in range(D)]
    return y[0]


def orient(I, rule):
    (Ml, vl), (Mr, vr) = compose(I, rule[0]), compose(I, rule[1])
    weak = all(Ml[i][j] >= Mr[i][j] for i in range(D) for j in range(D)) and all(vl[i] >= vr[i] for i in range(D))
    return weak, weak and vl[0] > vr[0]


def part_b():
    print("B1. Orientation (natural numbers)")
    for system, rules in SYSTEMS.items():
        I = nat_interp(system)
        o = [orient(I, r) for r in rules]
        check(f"{system}: weakly orients all {len(rules)} rules, strictly none, (M_s)_00 = 1",
              all(w for w, _ in o) and not any(s for _, s in o) and all(I[c][0][0][0] == 1 for c in I))
    print("B2. Values on canonical strings")
    for system in SYSTEMS:
        I = nat_interp(system)
        f = T if system == "T" else H
        lead = system == "R_H"
        bad_formula = bad_incr = 0
        for n in range(2, 1 << 14):
            nbits = n.bit_length() - (0 if lead else 1)
            val = value(I, can_word(n, lead))
            bad_formula += val != 1 + (2 ** nbits) * (n % 3 == EXIT[system])
            y = f(n)
            if y is not None and y >= 2:
                bad_incr += value(I, can_word(y, lead)) > val
        rhs = "1 + 2^l(n) [n = 1 mod 3]" if lead else f"1 + 2^(l(n)-1) [n = {EXIT[system]} mod 3]"
        check(f"{system}: Phi = {rhs}, not increasing along the map", bad_formula == 0 and bad_incr == 0,
              "(2 <= n < 2^14)")
    print("B3. The residue component")
    I = nat_interp("T")
    blk = [1, 2, 3]
    gens = [[[I[c][0][i][j] for j in blk] for i in blk] for c in ("f", "t")]
    pat = lambda A: tuple(tuple(int(x > 0) for x in row) for row in A)  # noqa: E731
    seen, frontier = {pat(g) for g in gens}, [pat(g) for g in gens]
    while frontier:
        P = frontier.pop()
        for g in gens:
            Q = tuple(tuple(int(any(P[i][k] and pat(g)[k][j] for k in range(3))) for j in range(3)) for i in range(3))
            if Q not in seen:
                seen.add(Q)
                frontier.append(Q)
    perms = all(sum(row) == 1 for P in seen for row in P) and \
        all(sum(P[i][j] for i in range(3)) == 1 for P in seen for j in range(3))
    check("the support patterns are the 6 permutations; no positive matrix ((P) fails)",
          len(seen) == 6 and perms and not any(all(all(row) for row in P) for P in seen))
    growth = True
    for k in range(1, 9):
        for w in itertools.product((0, 1), repeat=k):
            A = gens[w[0]]
            for b in w[1:]:
                A = [[sum(A[i][m] * gens[b][m][j] for m in range(3)) for j in range(3)] for i in range(3)]
            growth &= all(sorted(row) == [0, 0, 2 ** k] for row in A)
    check("every product of length k is 2^k times a permutation matrix (growth rate log 2)", growth,
          "(all words of length <= 8)")
    rel = []
    for system in SYSTEMS:
        Is = nat_interp(system)
        start = 1 + (ENTRY[system] if system != "R_H" else (2 * ENTRY[system] + 1) % 3)
        reached, stack = {start}, [start]
        while stack:
            x = stack.pop()
            for c in ("f", "t"):
                for y in range(D):
                    if Is[c][0][x][y] > 0 and y not in reached:
                        reached.add(y)
                        stack.append(y)
        rel.append(start in blk and (1 + EXIT[system]) in reached)
    check("the component is entered from the left end and reaches the right end for T, H and R_H",
          rel == [True, True, True])
    print("B4. The form of paper I")
    u = c = [1, 1, 0, 0]

    def phi1(n):
        v = u[:]
        for ch in bin(n)[2:]:
            M = I["ft"[int(ch)]][0]
            v = [sum(v[i] * M[i][j] for i in range(D)) for j in range(D)]
        return sum(v[j] * c[j] for j in range(D))
    check("phi(n) = 1 + 2^l(n) [3 | n] and phi(T(n)) <= phi(n)",
          all(phi1(n) == 1 + (2 ** n.bit_length()) * (n % 3 == 0) and phi1(T(n)) <= phi1(n)
              for n in range(2, 1 << 14)), "(2 <= n < 2^14)")


def main():
    try:
        part_a()
        part_b()
    except CheckFailed as e:
        print(f"FAILED: {e}")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
