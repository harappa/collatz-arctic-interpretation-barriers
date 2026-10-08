#!/usr/bin/env python3
"""The block model of H (Proposition 7.2), the left-end digits, the carry families of H (Lemma 7.3) and the dependency
pair chains of H (Section 7 and Appendix C of the paper). Python 3, standard library only; a few seconds.

    python3 computations/check_hmodel.py

H(n) = 3n/4 on n = 0 mod 4 (letter a, written True below) and (9n+1)/8 on n = 7 mod 8 (letter b, False);
X = abb and Y = abbb are the blocks. One step of the Terras correspondence is that of `HModel.hStep`
(HModel/Defs.lean): from (m, r, c, a) for a word w, the next letter x gives r_{wx} = r_w + 2^{m_w} t_x and
c_{wx} = H(c_w + 3^{a_w} t_x), with t_x the least solution of c_w + 3^{a_w} t_x = 0 mod 4 (a) or = 7 mod 8 (b).

1. Terras correspondence: (m, r, c, a) = (8, 84, 80, 5) for X and (11, 1364, 1457, 7) for Y; the formula
   H^{|w|}(r_w + 2^{m_w} t) = c_w + 3^{a_w} t along w; the integers that follow a word form one residue class modulo
   2^{m_w} (exhaustively for 10 words); the numbers of bits 8#X + 11#Y and of factors 3, 5#X + 7#Y.
2. The affine constants gamma: 3^{a_w} r_w + gamma_w = 2^{m_w} c_w and gamma_{ww'} = 3^{a_{w'}} gamma_w + 2^{m_w}
   gamma_{w'} on 300 words; gamma_X = 68, gamma_Y = 868, gamma_XY - gamma_YX = 2^8 3^4; the translation of the Terras
   residue by a swap, -2^{m_phi+8} 3^{-(a_phi+8)} for H (400 examples) and -2^{m_phi+9} 3^{-(a_phi+7)} for T (200).
3. Left-end digits: in a step P -> 3P/4 the digit reaching the left end is floor(3P / 2^{l(P)-1}) - 3
   (4 <= P < 2^15, P = 0 mod 4), and the two digits of a step (9P+1)/8 (15 <= P < 2^15).
4. Uses of the dynamic rules along the family orbits ((ff., ttt.) = (k, 2#X + 3#Y)), the points of the orbit lie in
   Dom(H) in the class of their letter, and the block boundary points have the form of Proposition 7.2 (iii)
   (200 examples); the least point of the orbits for t = 1 and five short words is 255.
5. The carry families Z_H, O_H, F_H of Lemma 7.3: (i) the levels, (ii) the numbers of uses (at level k at least 2k,
   3k, and 5k - 1 for each of the four mixed rules, i.e. 2j+2, 3j+3, 5j+4 at level j+1) for k < 30 (k <= 11 for F_H),
   (iii) the points of level k with n >= k and l'(n) <= 20k + 20 for k < 40.
6. Dependency pair chains of H: in the reversed system the reversed rules of canDerivH(n), applied in the same order
   (each at its rightmost occurrence, which is the moving digit), lead from the reversed canonical string of n to that
   of H(n) (8 <= n < 2^13 in Dom(H), 3069 integers); root steps: one or two by pairs of P_B in the original system,
   one in the reversed system.

Prints ALL OK and exits with status 0 if every comparison succeeds; stops at the first failure with status 1.
"""
from __future__ import annotations

import random
import sys

sys.dont_write_bytecode = True


class CheckFailed(Exception):
    pass


def check(name: str, cond: bool, detail: str = "") -> None:
    if not cond:
        raise CheckFailed(f"{name}: comparison failed {detail}".rstrip())
    print(f"  [{name}] ok {detail}".rstrip())


# ---------------------------------------------------------------- the map, canonical derivations

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


def a_rule(b, d):
    s = 3 * b + d
    return ("ft"[b] + str(d), str(s // 2) + "ft"[s % 2])


def left_rule(d):
    return {0: ("/0", "/t"), 1: ("/1", "/ff"), 2: ("/2", "/ft")}[d]


def sweep(bits, d):
    out = []
    for b in bits:
        out.append(a_rule(b, d))
        d = (3 * b + d) // 2
    return out + [left_rule(d)]


FF, TTT = ("ff.", "0."), ("ttt.", "22.")


def can_deriv_h(n):
    if n % 4 == 0:
        return [FF] + sweep(tail_bits_lsb(n // 4), 0)
    if n % 8 == 7:
        m = (n - 7) // 8
        return [TTT] + sweep(tail_bits_lsb(m), 2) + sweep(tail_bits_lsb(3 * m + 2), 2)
    return []


def apply_seq(s, seq, last=False):
    """Apply the rules in order, each at its leftmost (or, with last=True, rightmost) occurrence."""
    for lhs, rhs in seq:
        i = s.rfind(lhs) if last else s.find(lhs)
        if i < 0:
            return None
        s = s[:i] + rhs + s[i + len(lhs):]
    return s


# ---------------------------------------------------------------- the Terras correspondence of H

def pow3mod8(a):
    return 1 if a % 2 == 0 else 3


def h_step(s, x):
    m, r, c, a = s
    if x:
        t0 = ((4 - c % 4) * pow3mod8(a)) % 4
        y = c + 3 ** a * t0
        if y % 4:
            raise CheckFailed("h_step: class a not reached")
        return (m + 2, r + (1 << m) * t0, H(y), a + 1)
    t0 = ((15 - c % 8) * pow3mod8(a)) % 8
    y = c + 3 ** a * t0
    if y % 8 != 7:
        raise CheckFailed("h_step: class b not reached")
    return (m + 3, r + (1 << m) * t0, H(y), a + 2)


def h_state(w):
    s = (0, 0, 0, 0)
    for x in w:
        s = h_step(s, x)
    return s


def letters_of(blocks):
    out = []
    for x in blocks:
        out += [True, False, False] if x else [True, False, False, False]
    return out


XW, YW = [True, False, False], [True, False, False, False]


def follows(n, w):
    for x in w:
        if (x and n % 4) or (not x and n % 8 != 7):
            return False
        n = H(n)
    return True


def gamma(w):
    m, r, c, a = h_state(w)
    return (1 << m) * c - 3 ** a * r


def gamma_rec(w):
    """gamma_{wa} = 3 gamma_w, gamma_{wb} = 9 gamma_w + 2^{m_w}."""
    g = m = 0
    for x in w:
        if x:
            g, m = 3 * g, m + 2
        else:
            g, m = 9 * g + (1 << m), m + 3
    return g


def t_terras(par):
    """Terras correspondence of T along the parity sequence par."""
    m, r, c, a = 0, 0, 0, 0
    for b in par:
        t0 = (b + c) % 2
        r += (1 << m) * t0
        y = c + 3 ** a * t0
        c = y // 2 if y % 2 == 0 else (3 * y + 1) // 2
        m += 1
        a += b
    return m, r, c, a


# ---------------------------------------------------------------- the checks

def part1():
    print("1. Terras correspondence of H")
    check("X = abb: (m, r, c, a) = (8, 84, 80, 5)", h_state(XW) == (8, 84, 80, 5))
    check("Y = abbb: (m, r, c, a) = (11, 1364, 1457, 7)", h_state(YW) == (11, 1364, 1457, 7))
    rng = random.Random(1)
    words = [XW, YW, XW + YW, YW + XW + XW] + [letters_of([rng.random() < 0.3 for _ in range(30)])]
    good = True
    for w in words:
        m, r, c, a = h_state(w)
        for t in (0, 1, 2, 12345, rng.getrandbits(200)):
            x = r + (1 << m) * t
            good &= follows(x, w)
            for _ in w:
                x = H(x)
            good &= x == c + 3 ** a * t
    check("r_w + 2^m t follows w and H^|w| of it is c_w + 3^a t", good)
    uniq = True
    for w in [[True], [False], [True, False], [False, True], XW, YW, XW + XW, XW + YW,
              [True, False, False, True], [False, False, True, False]]:
        m, r, _, _ = h_state(w)
        uniq &= [n for n in range(1 << m) if follows(n + (1 << m) * 5, w)] == [r]
    check("the integers that follow a word form one residue class mod 2^m", uniq, "(10 words, exhaustively)")
    shape = all(h_state(letters_of(b))[0] == sum(8 if x else 11 for x in b)
                and h_state(letters_of(b))[3] == sum(5 if x else 7 for x in b)
                for b in ([rng.random() < 0.5 for _ in range(rng.randint(0, 12))] for _ in range(100)))
    check("bits 8#X + 11#Y and factors 3: 5#X + 7#Y", shape, "(100 block words)")


def part2():
    print("2. Affine constants and the translation by a swap")
    rng0 = random.Random(3)
    aff = app = True
    for _ in range(300):
        w1 = [rng0.random() < 0.5 for _ in range(rng0.randint(0, 25))]
        w2 = [rng0.random() < 0.5 for _ in range(rng0.randint(0, 25))]
        m1, r1, c1, a1 = h_state(w1)
        _, _, _, a2 = h_state(w2)
        aff &= 3 ** a1 * r1 + gamma_rec(w1) == (1 << m1) * c1
        app &= gamma_rec(w1 + w2) == 3 ** a2 * gamma_rec(w1) + (1 << m1) * gamma_rec(w2)
    check("3^a r + gamma = 2^m c", aff, "(300 words)")
    check("gamma_{ww'} = 3^{a_w'} gamma_w + 2^{m_w} gamma_w'", app, "(300 pairs)")
    check("gamma_X = 68, gamma_Y = 868 (recursion and 2^m c - 3^a r)",
          (gamma_rec(XW), gamma_rec(YW), gamma(XW), gamma(YW)) == (68, 868, 68, 868))
    check("gamma_XY - gamma_YX = 2^8 3^4 = 20736", gamma(XW + YW) - gamma(YW + XW) == 2 ** 8 * 3 ** 4 == 20736)
    rng = random.Random(2)
    pieces = [XW, YW, [True], [False]]
    good = True
    for _ in range(400):
        phi = sum((rng.choice(pieces) for _ in range(rng.randint(0, 6))), [])
        chi = sum((rng.choice(pieces) for _ in range(rng.randint(0, 6))), [])
        m1, r1, _, _ = h_state(phi + XW + YW + chi)
        _, r2, _, _ = h_state(phi + YW + XW + chi)
        mp, _, _, ap = h_state(phi)
        M = 1 << m1
        good &= (r1 - (r2 - (1 << (mp + 8)) * pow(pow(3, -1, M), ap + 8, M))) % M == 0
    check("H: r_{phi XY chi} = r_{phi YX chi} - 2^{m_phi+8} 3^{-(a_phi+8)} mod 2^m", good, "(400 examples)")
    Xp, Yp = [1, 0, 1, 1, 0, 1, 1, 0], [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0]
    good = True
    for _ in range(200):
        phi = sum((rng.choice([Xp, Yp, [0], [1]]) for _ in range(rng.randint(0, 6))), [])
        chi = sum((rng.choice([Xp, Yp, [0], [1]]) for _ in range(rng.randint(0, 6))), [])
        m1, r1, _, _ = t_terras(phi + Xp + Yp + chi)
        _, r2, _, _ = t_terras(phi + Yp + Xp + chi)
        mp, _, _, ap = t_terras(phi)
        M = 1 << m1
        good &= (r1 - (r2 - (1 << (mp + 9)) * pow(pow(3, -1, M), ap + 7, M))) % M == 0
    check("T: r_{phi X'Y' chi} = r_{phi Y'X' chi} - 2^{m_phi+9} 3^{-(a_phi+7)} mod 2^m", good, "(200 examples)")


def part3():
    print("3. Left-end digits")
    good = True
    for P in range(4, 1 << 15, 4):
        e = (3 * P) // (1 << (P.bit_length() - 1)) - 3
        seq = can_deriv_h(P)
        good &= [seq.count(left_rule(d)) for d in range(3)] == [int(d == e) for d in range(3)]
    check("step 3P/4: the digit reaching the left end is floor(3P / 2^(l(P)-1)) - 3", good, "(4 <= P < 2^15)")
    good = True
    for P in range(15, 1 << 15, 8):
        m = (P - 7) // 8
        y2 = 3 * m + 2
        e1 = y2 // (1 << (m.bit_length() - 1)) - 3
        e2 = (3 * y2 + 2) // (1 << (y2.bit_length() - 1)) - 3
        exp = [0, 0, 0]
        exp[e1] += 1
        exp[e2] += 1
        good &= [can_deriv_h(P).count(left_rule(d)) for d in range(3)] == exp
    check("step (9P+1)/8: the two digits", good, "(15 <= P < 2^15)")


def min_orbit(blocks):
    w = letters_of(blocks)
    m, r, _, _ = h_state(w)
    x, mn = r + (1 << m), None
    for _ in w:
        mn = x if mn is None else min(mn, x)
        x = H(x)
    return mn


def part4():
    print("4. Family orbits: dynamic rules, domain and block boundary points")
    rng = random.Random(7)
    good5 = good6 = True
    for _ in range(200):
        blocks = [rng.random() < 0.3 for _ in range(rng.randint(1, 25))]
        w = letters_of(blocks)
        m, r, c, a = h_state(w)
        t = rng.randint(1, 1 << 40)
        x = r + (1 << m) * t
        cff = cttt = 0
        bstart, pos = [], 0
        for b in blocks:
            bstart.append(pos)
            pos += 3 if b else 4
        for i, letter in enumerate(w):
            good5 &= in_dom(x) and ((x % 4 == 0) if letter else (x % 8 == 7))
            if i in bstart:
                k = bstart.index(i)
                mp, _, cp, ap = h_state(letters_of(blocks[:k]))
                q, rem = divmod(x - cp, 3 ** ap)
                rp = q - (1 << (m - mp)) * t
                good6 &= rem == 0 and 0 <= rp < (1 << (m - mp)) and x % 4 == 0
            seq = can_deriv_h(x)
            cff += seq.count(FF)
            cttt += seq.count(TTT)
            x = H(x)
        good5 &= x == c + 3 ** a * t
        nx = sum(blocks)
        good5 &= (cff, cttt) == (len(blocks), 2 * nx + 3 * (len(blocks) - nx))
    check("(ff., ttt.) uses = (k, 2#X + 3#Y); the orbit points lie in Dom(H) in the class of their letter", good5,
          "(200 examples)")
    check("boundary points P_i = c_<i + 3^{a_i} (r' + 2^{m-L_i} t), 0 <= r' < 2^{m-L_i}, P_i = 0 mod 4", good6,
          "(200 examples)")
    mn = min(min_orbit(b) for b in ([True], [False], [True, True], [False, True], [True, False, False]))
    check("least orbit point for t = 1", mn == 255, f"({mn})")


def part5():
    print("5. Carry families of H")
    rng = random.Random(9)
    good = True
    for k in range(1, 30):
        z = rng.randint(1, 1000)
        n = 4 ** (k + 1) * z
        good &= H(n) == 4 ** k * 3 * z and can_deriv_h(n).count(a_rule(0, 0)) >= 2 * k
    check("Z_H: n = 4^(k+1) z -> 4^k (3z); f0 -> 0f used >= 2k times", good, "(k < 30)")
    good = True
    for k in range(1, 30):
        z = rng.randint(1, 1000)
        n = 8 ** (k + 1) * (z + 1) - 1
        good &= n % 8 == 7 and H(n) + 1 == 8 ** k * (9 * z + 9)
        good &= can_deriv_h(n).count(a_rule(1, 2)) >= 3 * k
    check("O_H: n + 1 = 8^(k+1)(z+1) -> 8^k (9z+9); t2 -> 2t used >= 3k times", good, "(k < 30)")
    mixed = [a_rule(0, 1), a_rule(1, 0), a_rule(1, 1), a_rule(0, 2)]
    good = True
    for k in range(1, 12):
        w0 = rng.randint(0, 1000)
        num = 3 + 8 * (1 << (20 * k)) * (5 * w0 + 4)
        n = num // 5
        good &= num % 5 == 0
        y2 = 3 * ((n - 7) // 8) + 2
        good &= 5 * y2 + 2 == 16 ** (5 * k) * (5 * (3 * w0 + 2) + 2)
        x, word = n, ""
        for _ in range(8):
            good &= in_dom(x)
            word += "a" if x % 4 == 0 else "b"
            x = H(x)
        good &= word == "babababa"
        q, rem = divmod(5 * x - 3, 8 * (1 << (20 * (k - 1))))
        good &= rem == 0 and q % 5 == 4 and (q - 4) // 5 == 531441 * w0 + 425152
        good &= all(can_deriv_h(n).count(rule) >= 5 * k - 1 for rule in mixed)
    check("F_H: 5n = 3 + 8 2^(20k)(5w+4); 8 steps babababa to level k-1; f1, t0, t1, f2 used >= 5k - 1 times",
          good, "(k <= 11)")
    good = True
    for k in range(0, 40):
        nz = 4 ** (k + 1)
        no = 2 * 8 ** (k + 1) - 1
        nf = (3 + 32 * (1 << (20 * k))) // 5
        good &= (3 + 32 * (1 << (20 * k))) % 5 == 0
        good &= nz % 4 ** (k + 1) == 0 and (no + 1) % 8 ** (k + 1) == 0 and (no + 1) // 8 ** (k + 1) >= 2
        good &= (5 * nf - 3) % (8 * (1 << (20 * k))) == 0 and ((5 * nf - 3) // (8 * (1 << (20 * k)))) % 5 == 4
        good &= all(k <= n and n.bit_length() - 1 <= 20 * k + 20 for n in (nz, no, nf))
    check("(iii) every level k has a point n >= k with l'(n) <= 20k + 20", good, "(k < 40)")


def part6():
    print("6. Dependency pair chains of H")
    bad = cnt = 0
    roots = True
    for n in range(8, 1 << 13):
        if not in_dom(n):
            continue
        seq = can_deriv_h(n)
        rseq = [(l[::-1], r[::-1]) for l, r in seq]
        w = "." + binp(n)[::-1] + "/"
        cnt += 1
        bad += apply_seq(w, rseq, last=True) != "." + binp(H(n))[::-1] + "/"
        roots &= sum(1 for l, _ in seq if l[0] == "/") == (1 if n % 4 == 0 else 2)
        roots &= sum(1 for l, _ in rseq if l[0] == ".") == 1
    check("reversed chains (reversed rules, same order, at the moving digit)", bad == 0 and cnt == 3069,
          f"({cnt} integers)")
    check("root steps: original one (a) or two (b), reversed one", roots)


def main():
    try:
        part1()
        part2()
        part3()
        part4()
        part5()
        part6()
    except CheckFailed as e:
        print(f"FAILED: {e}")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
