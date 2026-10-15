#!/usr/bin/env python3
"""Independent checker for the certificate files of Theorem 8.3 (labelling and tiling).

Usage: python3 computations/check_certificates.py [DIR]

DIR defaults to computations/certificates next to this script.  The program
recomputes the transformed systems (flat context closure with root labelling,
full tiling of width 2 and 3) of collatz-T and its reversal from the eleven
rules of the paper, and checks for every certificate file:

  (1) the sizes of the transformed system and of its dependency pairs;
  (2) every listed pair is a dependency pair L# -> R# with L -> R a rule;
  (3) every witness is an actual chain: an original rewrite sequence whose
      image starts and ends with root steps by the stated pairs and has only
      steps below the root in between;
  (4) for innermost certificates, every transformed step is innermost;
  (5) the proved edges make the set of pairs strongly connected;
  (6) every locality entry is the canonical step of E(n) for a number n with
      the stated key, and its root steps use exactly the stated pairs;
  (7) the pairs of the locality entries of the relevant keys are exactly the
      listed pairs (P_E is the set of pairs used at the root, Section 8.2).

It uses only the Python standard library and does not import the generator.
"""

import json
import os
import sys
import time

SIG = "/.ft012"
BITS = "ft"
DIGITS = "012"

# collatz-T (Table 1 of the paper): dynamic, carry, left-end rules.
RULES_T = [
    ("f.", "."), ("t.", "2."),
    ("f0", "0f"), ("f1", "0t"), ("f2", "1f"),
    ("t0", "1t"), ("t1", "2f"), ("t2", "2t"),
    ("/0", "/t"), ("/1", "/ff"), ("/2", "/ft"),
]

# B(d) = bin'(3 + d): the binary digits of 3 + d without the leading 1.
B_OF = {"0": "t", "1": "ff", "2": "ft"}

EXPECTED = {
    ("T", "rootlabel"): (413, 496),
    ("Trev", "rootlabel"): (455, 561),
    ("T", "tile2"): (539, 917),
    ("Trev", "tile2"): (539, 749),
    ("T", "tile3"): (26411, 56252),
    ("Trev", "tile3"): (26411, 51793),
}

EXPECTED_FILES = [
    "%s-%s-%s.json" % (s, t, c)
    for s in ("T", "Trev")
    for t in ("rootlabel", "tile2", "tile3")
    for c in ("full", "innermost")
]


class CheckError(Exception):
    """A failed check, with a human-readable description."""


def fail(msg):
    raise CheckError(msg)


# ---------------------------------------------------------------------------
# Original systems

def self_check_rules():
    """Check that the hard-coded rules are the carry/left-end rules of the paper."""
    val = {"f": 0, "t": 1}
    for l, r in RULES_T[2:8]:
        b, d = l
        d2, b2 = r
        if 3 * val[b] + int(d) != 2 * int(d2) + val[b2]:
            fail("carry rule %s->%s violates 3b+d = 2d'+b'" % (l, r))
    for l, r in RULES_T[8:]:
        if r != "/" + B_OF[l[1]]:
            fail("left-end rule %s->%s is not /d -> / bin'(3+d)" % (l, r))
        if int("1" + B_OF[l[1]].replace("f", "0").replace("t", "1"), 2) != 3 + int(l[1]):
            fail("B(%s) is not bin'(3+%s)" % (l[1], l[1]))


def original_rules(system):
    """The rules of T or T^rev as a list of (l, r) strings."""
    if system == "T":
        return list(RULES_T)
    if system == "Trev":
        return [(l[::-1], r[::-1]) for l, r in RULES_T]
    fail("unknown system %r" % system)


def root_preserving(l, r):
    return l[0] == r[0]


# ---------------------------------------------------------------------------
# Transformations: strings and rules

def lab(s, g):
    """Root labelling of a string: each letter labelled by its right neighbour, the last by g."""
    t = s + g
    return tuple(t[i] + t[i + 1] for i in range(len(s)))


def tiles(s, w):
    """The windows of width w of a string."""
    return tuple(s[i:i + w] for i in range(len(s) - w + 1))


def words(n):
    """All strings of length n over SIG."""
    out = [""]
    for _ in range(n):
        out = [u + a for u in out for a in SIG]
    return out


def transformed_rules(rules, trans):
    """The rule set R' of the transformed system, as a set of (L, R) symbol tuples."""
    out = set()
    if trans == "rootlabel":
        closed = []
        for l, r in rules:
            if root_preserving(l, r):
                closed.append((l, r))
            else:
                closed.extend((s + l, s + r) for s in SIG)
        for l, r in closed:
            for g in SIG:
                out.add((lab(l, g), lab(r, g)))
    elif trans in ("tile2", "tile3"):
        w = int(trans[-1])
        ctx = words(w - 1)
        for l, r in rules:
            for x in ctx:
                for y in ctx:
                    out.add((tiles(x + l + y, w), tiles(x + r + y, w)))
    else:
        fail("unknown transformation %r" % trans)
    return out


def dependency_pairs(rset):
    """All dependency pairs (L, R') with R' a non-empty suffix of R whose first symbol is defined."""
    defined = {L[0] for L, _ in rset}
    pairs = set()
    for L, R in rset:
        for i in range(len(R)):
            if R[i] in defined:
                pairs.add((L, R[i:]))
    return pairs, defined


def image(s, trans):
    """The image of an original string in the transformed system."""
    if trans == "rootlabel":
        return lab(s, ".")
    w = int(trans[-1])
    pad = "." * (w - 1)
    return tiles(pad + s + pad, w)


def image_step(s, p, l, r, trans):
    """The transformed step (q, L, R) of the original step at position p by l -> r on s."""
    if trans == "rootlabel":
        end = p + len(l)
        g = s[end] if end < len(s) else "."
        if root_preserving(l, r):
            return p, lab(s[p:end], g), lab(r, g)
        if p < 1:
            fail("non-root-preserving rule %s->%s applied at position 0" % (l, r))
        return p - 1, lab(s[p - 1:end], g), lab(s[p - 1] + r, g)
    w = int(trans[-1])
    pad = "." * (w - 1)
    ps = pad + s + pad
    pp = p + w - 1
    x = ps[pp - (w - 1):pp]
    y = ps[pp + len(l):pp + len(l) + w - 1]
    return p, tiles(x + l + y, w), tiles(x + r + y, w)


# ---------------------------------------------------------------------------
# Context of one certificate file

class System:
    """The original and transformed system for one (system, transformation)."""

    def __init__(self, system, trans):
        self.system = system
        self.trans = trans
        self.rules = original_rules(system)
        self.rule_set = set(self.rules)
        self.rset = transformed_rules(self.rules, trans)
        self.pairs, self.defined = dependency_pairs(self.rset)
        lens = {}
        for L, _ in self.rset:
            lens.setdefault(len(L), set()).add(L)
        self.lhs_by_len = sorted(lens.items())

    def has_redex_from(self, img, start):
        """True if some left side of R' occurs in img at a position >= start."""
        for i in range(start, len(img)):
            for k, lset in self.lhs_by_len:
                if i + k <= len(img) and img[i:i + k] in lset:
                    return True
        return False

    def apply(self, s, step, where):
        """Apply an original step [p, l, r] to s; return (s', (q, L, R), img, img')."""
        if not (isinstance(step, list) and len(step) == 3):
            fail("%s: malformed step %r" % (where, step))
        p, l, r = step
        if (l, r) not in self.rule_set:
            fail("%s: %s->%s is not a rule of %s" % (where, l, r, self.system))
        if not (0 <= p and s[p:p + len(l)] == l):
            fail("%s: left side %r does not occur at position %d of %r" % (where, l, p, s))
        s2 = s[:p] + r + s[p + len(l):]
        q, L, R = image_step(s, p, l, r, self.trans)
        if (L, R) not in self.rset:
            fail("%s: transformed step %s -> %s is not a rule of R'" % (where, L, R))
        img, img2 = image(s, self.trans), image(s2, self.trans)
        if img[q:q + len(L)] != L:
            fail("%s: left side %s does not occur at position %d of the image" % (where, L, q))
        if img[:q] + R + img[q + len(L):] != img2:
            fail("%s: transformed step at %d does not give the image of %r" % (where, q, s2))
        return s2, (q, L, R), img, img2


def as_pair(obj, where):
    """Convert a JSON pair [L, R] to a tuple of symbol tuples."""
    if not (isinstance(obj, list) and len(obj) == 2
            and all(isinstance(x, list) and x for x in obj)):
        fail("%s: malformed pair %r" % (where, obj))
    return tuple(obj[0]), tuple(obj[1])


# ---------------------------------------------------------------------------
# Numbers and encodings

def T_map(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def bits_to_int(w):
    v = 0
    for c in w:
        v = 2 * v + (1 if c == "t" else 0)
    return v


def int_to_bits(v, k):
    return "".join("t" if (v >> (k - 1 - i)) & 1 else "f" for i in range(k))


def enc2(n):
    """E^(2)(n) = / d1 d2 w . with floor(n/2^nu) = 9 + 3 d1 + d2 in [9, 18)."""
    if n < 9:
        fail("E^(2)(%d) is not defined" % n)
    nu = 0
    while (n >> nu) >= 18:
        nu += 1
    top = n >> nu
    d1, d2 = divmod(top - 9, 3)
    return "/%d%d%s." % (d1, d2, int_to_bits(n - (top << nu), nu))


def parse_enc2(s, where):
    if not (len(s) >= 4 and s[0] == "/" and s[1] in DIGITS and s[2] in DIGITS
            and s[-1] == "." and all(c in BITS for c in s[3:-1])):
        fail("%s: start %r is not of the form / d1 d2 w ." % (where, s))
    w = s[3:-1]
    return (9 + 3 * int(s[1]) + int(s[2])) * 2 ** len(w) + bits_to_int(w)


def enc0rev(n):
    """The reversal of can(n): . rev(bin'(n)) /."""
    if n < 1:
        fail("E^(0)(%d) is not defined" % n)
    return "." + int_to_bits(n, n.bit_length())[1:][::-1] + "/"


def parse_enc0rev(s, where):
    if not (len(s) >= 2 and s[0] == "." and s[-1] == "/"
            and all(c in BITS for c in s[1:-1])):
        fail("%s: start %r is not of the form . rev(bin'(n)) /" % (where, s))
    return bits_to_int("t" + s[1:-1][::-1])


def rule_at(s, p, rules, where):
    """The unique rule of the given list whose left side occurs at position p."""
    hits = [(l, r) for l, r in rules if s[p:p + len(l)] == l]
    if len(hits) != 1:
        fail("%s: no unique rule applies at position %d of %r" % (where, p, s))
    return hits[0]


def canonical_steps_T(n, where):
    """The odd step of E^(2)(n) to E^(2)(T(n)) as a list of original steps (Section 8.2)."""
    carry = RULES_T[2:8]
    s = enc2(n)
    steps = []

    def do(p, rule):
        nonlocal s
        steps.append([p, rule[0], rule[1]])
        s = s[:p] + rule[1] + s[p + len(rule[0]):]

    if n % 2 != 1:
        fail("%s: n = %d is not odd" % (where, n))
    do(len(s) - 2, ("t.", "2."))
    i = len(s) - 2                      # position of the new ternary digit e
    while s[i - 1] in BITS:
        do(i - 1, rule_at(s, i - 1, carry, where))
        i -= 1
    if i != 3:
        fail("%s: the new digit stops at position %d, not 3" % (where, i))
    M = 9 * (3 + int(s[1])) + 3 * int(s[2]) + int(s[3])
    d1 = s[1]
    do(0, ("/" + d1, "/" + B_OF[d1]))
    k = len(B_OF[d1])
    for bi in range(k, 0, -1):          # rightmost bit of B(d1) first
        for pos in (bi, bi + 1):        # across both ternary digits
            do(pos, rule_at(s, pos, carry, where))
    if s != enc2(T_map(n)):
        fail("%s: canonical step ends in %r, not E^(2)(T(%d)) = %r"
             % (where, s, n, enc2(T_map(n))))
    return steps, M


def canonical_steps_Trev(n, where):
    """The step of E^(0)(n) to E^(0)(T(n)) for T^rev as a list of original steps."""
    rcarry = [(l[::-1], r[::-1]) for l, r in RULES_T[2:8]]
    s = enc0rev(n)
    steps = []

    def do(p, rule):
        nonlocal s
        steps.append([p, rule[0], rule[1]])
        s = s[:p] + rule[1] + s[p + len(rule[0]):]

    if s[1] == "f":
        do(0, (".f", "."))
    elif s[1] == "t":
        do(0, (".t", ".2"))
        i = 1
        while s[i + 1] in BITS:
            do(i, rule_at(s, i, rcarry, where))
            i += 1
        d = s[i]
        if s[i + 1] != "/":
            fail("%s: the ternary digit is not followed by /" % where)
        do(i, (d + "/", B_OF[d][::-1] + "/"))
    else:
        fail("%s: no dynamic rule applies to %r" % (where, s))
    if s != enc0rev(T_map(n)):
        fail("%s: canonical step ends in %r, not E^(0)(T(%d)) reversed = %r"
             % (where, s, n, enc0rev(T_map(n))))
    return steps


# ---------------------------------------------------------------------------
# Checks of one file

def strongly_connected(n, edges):
    """True if the directed graph on range(n) with the given edges is strongly connected."""
    if n <= 1:
        return True
    fwd = {i: set() for i in range(n)}
    bwd = {i: set() for i in range(n)}
    for a, b in edges:
        fwd[a].add(b)
        bwd[b].add(a)

    def reach(adj):
        seen, stack = {0}, [0]
        while stack:
            for v in adj[stack.pop()]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return seen

    return len(reach(fwd)) == n and len(reach(bwd)) == n


def check_file(path, cache):
    """Check one certificate file; return a summary dict or raise CheckError."""
    name = os.path.basename(path)
    with open(path, encoding="utf-8") as fh:
        data = json.load(fh)
    system, trans = data.get("system"), data.get("transformation")
    chains, enc = data.get("chains"), data.get("encoding")
    if (system, trans) not in EXPECTED:
        fail("%s: unknown system/transformation %r/%r" % (name, system, trans))
    if chains not in ("full", "innermost"):
        fail("%s: unknown chains %r" % (name, chains))
    if enc != {"T": "E2", "Trev": "E0"}[system]:
        fail("%s: encoding %r does not match system %s" % (name, enc, system))
    if name != "%s-%s-%s.json" % (system, trans, chains):
        fail("%s: file name does not match its header" % name)

    # (1) sizes
    key = (system, trans)
    if key not in cache:
        cache[key] = System(system, trans)
    S = cache[key]
    exp_rules, exp_pairs = EXPECTED[key]
    if len(S.rset) != exp_rules or len(S.pairs) != exp_pairs:
        fail("%s: |R'| = %d, |DP| = %d, expected %d, %d"
             % (name, len(S.rset), len(S.pairs), exp_rules, exp_pairs))

    # (2) the listed pairs
    pairs = [as_pair(x, "%s pair %d" % (name, i)) for i, x in enumerate(data["pairs"])]
    if len(set(pairs)) != len(pairs):
        fail("%s: the list of pairs has duplicates" % name)
    for i, (L, R) in enumerate(pairs):
        if (L, R) not in S.rset:
            fail("%s: pair %d %s -> %s is not L# -> R# for a rule L -> R of R'" % (name, i, L, R))
        if R[0] not in S.defined or (L, R) not in S.pairs:
            fail("%s: pair %d is not a dependency pair (%s not defined)" % (name, i, R[0]))

    # (3), (4) witnesses
    edges = set()
    nsteps = 0
    innermost = chains == "innermost"
    for wi, wit in enumerate(data["witnesses"]):
        where = "%s witness %d" % (name, wi)
        a, b = wit["edge"]
        if not (0 <= a < len(pairs) and 0 <= b < len(pairs)):
            fail("%s: edge %r out of range" % (where, wit["edge"]))
        steps = wit["steps"]
        if len(steps) < 2:
            fail("%s: fewer than two steps" % where)
        s = wit["start"]
        if not (s and all(c in SIG for c in s)):
            fail("%s: start %r is not a non-empty string over %s" % (where, s, SIG))
        for si, step in enumerate(steps):
            w2 = "%s step %d" % (where, si)
            s, (q, L, R), img, _ = S.apply(s, step, w2)
            nsteps += 1
            if si == 0 or si == len(steps) - 1:
                want = pairs[a] if si == 0 else pairs[b]
                if q != 0:
                    fail("%s: expected a root step by pair %d, got a step at position %d"
                         % (w2, a if si == 0 else b, q))
                if (L, R) != want:
                    fail("%s: root step by %s -> %s, expected pair %d %s -> %s"
                         % (w2, L, R, a if si == 0 else b, want[0], want[1]))
                if R[0] not in S.defined:
                    fail("%s: root step is not a dependency pair step" % w2)
            elif q < 1:
                fail("%s: step at the root between the two pair steps" % w2)
            if innermost and S.has_redex_from(img, q + 1 if q >= 1 else 1):
                fail("%s: step at position %d is not innermost (a left side of R' "
                     "occurs further right)" % (w2, q))
        edges.add((a, b))

    # (5) strong connectivity
    if not strongly_connected(len(pairs), edges):
        fail("%s: the proved edges do not make the %d pairs strongly connected"
             % (name, len(pairs)))

    # (6) locality
    keys = set()
    loc_pairs = set()
    for li, ent in enumerate(data["locality"]):
        where = "%s locality %d (key %r)" % (name, li, ent.get("key"))
        start = ent["start"]
        if system == "T":
            n = parse_enc2(start, where)
            if n < 2 * 3 ** 3 + 8:
                fail("%s: n = %d < 2*3^3+8" % (where, n))
            if n % 2 != 1:
                fail("%s: n = %d is even" % (where, n))
            t = T_map(n)
            nu = 0
            while (t >> nu) >= 54:
                nu += 1
            M = t >> nu
            if not 27 <= M < 54:
                fail("%s: M = %d not in [27, 54)" % (where, M))
            steps, M2 = canonical_steps_T(n, where)
            if M2 != M:
                fail("%s: digits before the left-end step give M = %d, not %d" % (where, M2, M))
            if ent["key"] != M:
                fail("%s: key %r, but M = %d for n = %d" % (where, ent["key"], M, n))
        else:
            n = parse_enc0rev(start, where)
            if n < 16:
                fail("%s: n = %d < 16" % (where, n))
            if ent["key"] != n % 16:
                fail("%s: key %r, but n mod 16 = %d for n = %d" % (where, ent["key"], n % 16, n))
            steps = canonical_steps_Trev(n, where)
        if ent["key"] in keys:
            fail("%s: key occurs twice" % where)
        keys.add(ent["key"])
        s = start
        used = []
        for si, step in enumerate(steps):
            s, (q, L, R), _, _ = S.apply(s, step, "%s canonical step %d" % (where, si))
            if q == 0:
                if R[0] not in S.defined:
                    fail("%s: root step %s -> %s is not a dependency pair step" % (where, L, R))
                used.append((L, R))
        given = [as_pair(x, where) for x in ent["pairs"]]
        if used != given:
            fail("%s: root steps use %r, the entry lists %r" % (where, used, given))
        relevant = (system == "T") or (ent["key"] in (1, 2, 6, 9, 11))
        if relevant:
            loc_pairs.update(used)
    want_keys = set(range(27, 54)) if system == "T" else set(range(16))
    if keys != want_keys:
        fail("%s: locality keys %s, expected %s" % (name, sorted(keys), sorted(want_keys)))

    # (7) P_E is the set of pairs used at the root by the relevant keys
    if loc_pairs != set(pairs):
        fail("%s: pairs used by the locality table (relevant keys) differ from the listed "
             "pairs: missing %s, extra %s"
             % (name, sorted(set(pairs) - loc_pairs), sorted(loc_pairs - set(pairs))))

    return {"name": name, "rules": len(S.rset), "dps": len(S.pairs), "pairs": len(pairs),
            "witnesses": len(data["witnesses"]), "steps": nsteps, "edges": len(edges),
            "keys": len(keys)}


def main(argv):
    here = os.path.dirname(os.path.abspath(__file__))
    d = argv[1] if len(argv) > 1 else os.path.join(here, "certificates")
    t0 = time.time()
    try:
        self_check_rules()
        found = sorted(f for f in os.listdir(d) if f.endswith(".json"))
        if found != sorted(EXPECTED_FILES):
            fail("%s: expected the 12 files %s, found %s" % (d, sorted(EXPECTED_FILES), found))
        cache = {}
        for f in EXPECTED_FILES:
            r = check_file(os.path.join(d, f), cache)
            print("%-28s OK  |R'|=%d |DP|=%d |P_E|=%d witnesses=%d steps=%d edges=%d "
                  "locality keys=%d" % (r["name"], r["rules"], r["dps"], r["pairs"],
                                        r["witnesses"], r["steps"], r["edges"], r["keys"]))
    except CheckError as e:
        print("FAILED: %s" % e)
        return 1
    print("time %.1f s" % (time.time() - t0))
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
