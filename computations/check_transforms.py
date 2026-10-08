#!/usr/bin/env python3
"""The transformed systems of Section 8.2 of the paper (Appendix C). Python 3, standard library only; about half a
minute.

    python3 computations/check_transforms.py

For T (collatz-T) and its reversal, the script applies flat context closure with root labelling (Definitions 3 and 5
of [SM08], as in AProVE), full tiling of widths 2 and 3 without boundary symbols (`tile all` of matchbox), and the
dependency pair processors narrowing, rewriting and instantiation (Definition 28 of [GTSF06]), and checks:
- size: the numbers of rules and dependency pairs of the transformed systems;
- P_E and one SCC: the canonical derivations along the point family (Section 6.1, the model of T, with
  x_1 = x_0 = r_{sigma_0} mod 2^{s'}), in the encodings E^(0) and E^(2) (E^(j) lets the left-end rule wait for j
  digits; in an odd step the bits of bin'(3 + d_1) are then moved to the right across the j ternary digits, the
  rightmost bit first and each bit across all j digits before the next one, as in Section 8.2 of the paper and in
  steps_stack below), are mapped step by step to the transformed systems; the set P_E of pairs used at the root is
  strongly connected by observed edges (edges of actual chains, hence contained in every sound estimate), lies in one
  SCC of the estimated dependency graph EDG and of the estimated innermost dependency graph EIDG of [GTSF06,
  Definition 9], the rules used below the root are usable rules of P_E, and every pair of P_E is used with positive
  frequency per block. P_E is defined deterministically: for T, the pairs used at the root by the steps of all
  n >= 2*3^(j+1) + 8; for the reversal, by the steps of the n with n mod 16 in {1, 2, 6, 9, 11}; R_E is the set of
  rules used below the root by the same steps;
- symbols of E(n) (Theorem 8.3 (b)): every symbol of the transformed image of E(n) and E(T(n)) for these n and of
  every string along the family samples (the labelled or tiled symbols, including the label of the final '.' and the
  windows that contain the padding) occurs in P_E or R_E, the marked root symbol as a marked symbol of P_E, and
  R_E is contained in U(P_E). For all n of the range (n < 2^12), only the reversed tiling of width 3 has a symbol
  outside P_E and R_E, the window '.ff' of the n divisible by 4 (not a residue of the family);
- the pairs used only by general n (< 2^12): none for T; for the reversal those of parity windows that do not occur
  in the family; the residues modulo 16 of the points of the family are those of the windows of length 4 of
  concatenations of X' and Y';
- locality: the sequence of pairs used at the root is a function of the first 4 letters of bin'(T(n)) (T, E^(0)), of
  the stacked value (T, E^(2)), and of n mod 16 (reversal);
- innermost chains: in chains built by innermost rewriting, no pair of E^(0) occurs for the transformed systems, and
  the pairs of E^(2) all occur and are strongly connected by innermost edges; the canonical derivations of the
  reversal are innermost;
- processors: rewriting and instantiation change no pair of P_B or P_T^rev; narrowing (the full and the innermost
  versions agree) gives 12 pairs for P_B, 9 of them used by the family, and 4 pairs for P_T^rev, 3 of them used, with
  strong connectivity (also by innermost edges) and usable rules as above;
- usable rules and usable symbols: the complement of U(P_E) consists of rules starting with a root-type symbol, and
  the steps below the root use none of them; the letters of P_E and of the rules used are usable symbols
  ([LPAR04, Theorem 28]);
- the uses in the reversal are deterministic (the windows 1011, 0110, 1101 occur inside each block, 1010 and 0101 at
  each junction).
The chains are generated with a fixed seed; each observed edge is an actual chain and proves that the edge exists.
The frequencies printed are observations and are not used in the proofs.

Prints ALL OK and exits with status 0 if every comparison succeeds; stops at the first failure with status 1.
"""
import random
import sys

sys.dont_write_bytecode = True
sys.setrecursionlimit(100000)

SIG = "/.ft012"
DT = [("f.", "."), ("t.", "2.")]
AR = [("f0", "0f"), ("f1", "0t"), ("f2", "1f"), ("t0", "1t"), ("t1", "2f"), ("t2", "2t")]
BR = [("/0", "/t"), ("/1", "/ff"), ("/2", "/ft")]
ST = DT + AR + BR
BL = {"0": "t", "1": "ff", "2": "ft"}              # left-end rule /d -> /B(d)
AMAP = {(l[0], l[1]): (r[0], r[1]) for l, r in AR}  # b d -> d' b'


class CheckFailed(Exception):
    pass


def check(name, got, expect):
    if got != expect:
        raise CheckFailed(f"{name}: got {got}, expected {expect}")
    print(f"  [{name}] ok {got}")


def require(cond, *info):
    if not cond:
        raise CheckFailed("internal comparison failed: " + " ".join(map(str, info)))


def rev(R):
    return [(l[::-1], r[::-1]) for l, r in R]


# ---------------------------------------------------------------- transformations

class Ident:
    """No transformation; symbols are single letters."""
    name = "none"

    def __init__(self, R):
        self.R = [(tuple(l), tuple(r)) for l, r in R]

    def rules(self):
        return self.R

    def map(self, s, p, l, r):
        return tuple(s[p:p + len(l)]), tuple(r), p

    def tpos(self, s, p, l, r):
        return p

    def image(self, s):
        """The symbols of the string s (the first one is the marked root)."""
        return tuple(s)


class FCRL:
    """Flat context closure ([SM08], Definition 5) followed by root labelling (Definition 3). A symbol is a letter
    together with its right neighbour. The label of the last letter of a string is Z (the root of the variable; as in
    Example 9 of [SM08], every rule is copied for the 7 values of Z)."""
    name = "FC+rl"
    Z = "."

    def __init__(self, R):
        self.Rp = [(l, r) for l, r in R if l[0] == r[0]]
        self.Ra = [(l, r) for l, r in R if l[0] != r[0]]
        self.fc = self.Rp + [(a + l, a + r) for l, r in self.Ra for a in SIG]
        out = set()
        for l, r in self.fc:
            for g in SIG:
                out.add((self.lab(l, g), self.lab(r, g)))
        self.R = sorted(out)

    @staticmethod
    def lab(w, g):
        return tuple(w[i] + (w[i + 1] if i + 1 < len(w) else g) for i in range(len(w)))

    def rules(self):
        return self.R

    def tpos(self, s, p, l, r):
        return p if l[0] == r[0] else p - 1

    def map(self, s, p, l, r):
        q = self.tpos(s, p, l, r)
        L = s[q:p + len(l)]
        Rr = s[q:p] + r
        g = s[p + len(l)] if p + len(l) < len(s) else self.Z
        return self.lab(L, g), self.lab(Rr, g), q

    def image(self, s):
        """The labelled image of the string s (the first symbol is the marked root; the last letter, '.', is labelled
        by Z)."""
        return self.lab(s, self.Z)


class Tile:
    """Full tiling of width w without boundary symbols: every rule is closed under all contexts of length w-1 on both
    sides and rewritten as windows of width w. Canonical strings are embedded with w-1 letters '.' added on each side
    (the added letters do not take part in rewriting)."""

    def __init__(self, R, w):
        self.w = w
        self.name = f"tiling w={w}"
        out = set()
        ctx = [""]
        for _ in range(w - 1):
            ctx = [c + a for c in ctx for a in SIG]
        for l, r in R:
            for x in ctx:
                for y in ctx:
                    out.add((self.tiles(x + l + y), self.tiles(x + r + y)))
        self.R = sorted(out)
        self.pad = "." * (w - 1)

    def tiles(self, u):
        w = self.w
        return tuple(u[i:i + w] for i in range(len(u) - w + 1))

    def rules(self):
        return self.R

    def tpos(self, s, p, l, r):
        return p

    def map(self, s, p, l, r):
        w = self.w
        ps = self.pad + s + self.pad
        pp = p + (w - 1)
        x = ps[pp - (w - 1):pp]
        y = ps[pp + len(l):pp + len(l) + w - 1]
        return self.tiles(x + l + y), self.tiles(x + r + y), p

    def image(self, s):
        """The tiled image of s padded with w-1 letters '.' on each side (the first window is the marked root)."""
        return self.tiles(self.pad + s + self.pad)


# ---------------------------------------------------------------- dependency pairs, graphs, usable rules

def dps(R):
    D = {l[0] for l, _ in R}
    P = set()
    for l, r in R:
        for i in range(len(r)):
            if r[i] in D:
                P.add((l, r[i:]))
    return D, sorted(P)


class Normal:
    """Normal forms: whether a left-hand side occurs in the letters below the marked root."""

    def __init__(self, R):
        self.lhs = {l for l, _ in R}
        self.lens = sorted({len(l) for l in self.lhs})

    def ok(self, u):
        n = len(u)
        for k in self.lens:
            for i in range(n - k + 1):
                if tuple(u[i:i + k]) in self.lhs:
                    return False
        return True


def cap(t, D):
    """cap of [GTSF06, Definition 9]: below the (marked) root, everything from the first defined symbol on becomes a
    fresh variable. Returns (the letters below the root, whether the end is still the original variable x)."""
    for i in range(1, len(t)):
        if t[i] in D:
            return t[1:i], False
    return t[1:], True


def graph(P, D, innermost=False, NF=None):
    """EDG (innermost=False) and EIDG (innermost=True) of [GTSF06, Definition 9]: EDG has an edge if ren(cap(t)) and v
    unify, EIDG if cap(t) and v unify with an mgu mu such that s mu and v mu are normal forms. Edges go through relay
    vertices (numbered from len(P)), one for each type of capped right-hand side (i -> relay -> j is equivalent to the
    edge i -> j, so the SCCs of pairs do not change). Returns (number of pairs, adjacency lists, self-loops)."""
    n = len(P)
    by_root = {}
    for j, (v, _) in enumerate(P):
        by_root.setdefault(v[0], []).append(j)
    okl = [True] * n
    if innermost:
        okl = [NF.ok(v[1:]) for v, _ in P]
    hub = {}
    adj = [[] for _ in range(n)]
    tails = []
    for i, (s, t) in enumerate(P):
        if innermost and not okl[i]:
            continue
        cur, isx = cap(t, D)
        key = (t[0], cur, isx, s[1:][max(0, len(s) - NF.lens[-1]):] if (innermost and isx) else None)
        h = hub.get(key)
        if h is None:
            h = n + len(tails)
            hub[key] = h
            tg = []
            Ssuf = key[3]
            for j in by_root.get(t[0], ()):
                if innermost and not okl[j]:
                    continue
                V = P[j][0][1:]
                m = min(len(cur), len(V))
                if cur[:m] != V[:m]:
                    continue
                if innermost:
                    if len(V) > len(cur):
                        if isx and not NF.ok(Ssuf + V[len(cur):]):
                            continue
                    elif len(cur) > len(V):
                        if not NF.ok(V + cur[len(V):]):
                            continue
                tg.append(j)
            tails.append(tg)
        adj[i].append(h)
    adj.extend(tails)
    loops = {i for i in range(n) if adj[i] and i in tails[adj[i][0] - n]}
    return n, adj, loops


def sccs(n, adj):
    """Tarjan's algorithm, iterative."""
    index = [0] * n
    low = [0] * n
    seen = [False] * n
    onst = [False] * n
    st = []
    out = []
    c = 1
    for v0 in range(n):
        if seen[v0]:
            continue
        work = [(v0, 0)]
        while work:
            v, k = work.pop()
            if k == 0:
                seen[v] = True
                index[v] = low[v] = c
                c += 1
                st.append(v)
                onst[v] = True
            if k < len(adj[v]):
                work.append((v, k + 1))
                w = adj[v][k]
                if not seen[w]:
                    work.append((w, 0))
                elif onst[w]:
                    low[v] = min(low[v], index[w])
                continue
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop()
                    onst[w] = False
                    comp.append(w)
                    if w == v:
                        break
                out.append(comp)
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    return out


def nontrivial(g):
    """Nontrivial SCCs of pairs (without relay vertices: two or more pairs, or a self-loop)."""
    n, adj, loops = g
    res = []
    for comp in sccs(len(adj), adj):
        c = sorted(v for v in comp if v < n)
        if len(c) > 1 or (len(c) == 1 and c[0] in loops):
            res.append(c)
    return res


def usable(R, rhss, D):
    need = set()
    for r in rhss:
        need |= {ch for ch in r[1:] if ch in D}
    by_first = {}
    for l, r in R:
        by_first.setdefault(l[0], []).append((l, r))
    U = set()
    todo = list(need)
    while todo:
        a = todo.pop()
        for l, r in by_first.get(a, ()):
            if (l, r) not in U:
                U.add((l, r))
                for ch in r:
                    if ch in D and ch not in need:
                        need.add(ch)
                        todo.append(ch)
    return U


def strongly_connected(nodes, edges):
    """Whether the nodes form one strongly connected set using the (observed) edges only."""
    nodes = sorted(nodes)
    if not nodes:
        return False
    fw = {v: set() for v in nodes}
    bw = {v: set() for v in nodes}
    for a, b in edges:
        fw.setdefault(a, set()).add(b)
        bw.setdefault(b, set()).add(a)

    def reach(g, s):
        seen = {s}
        todo = [s]
        while todo:
            v = todo.pop()
            for w in g.get(v, ()):
                if w not in seen:
                    seen.add(w)
                    todo.append(w)
        return seen
    f = reach(fw, nodes[0])
    b = reach(bw, nodes[0])
    return all(v in f and v in b for v in nodes)


# ---------------------------------------------------------------- Collatz and the point family

def T(n):
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def binp(n):
    """bin'(n): the binary digits of n without the leading 1 (f = 0, t = 1)."""
    return "".join("t" if c == "1" else "f" for c in bin(n)[3:])


BX = [1, 0, 1, 1, 0, 1, 1, 0]
BY = [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0]


def terras(sig):
    """The residue r (mod 2^m) following the parity sequence sig, c = T^m(r), and the number A of odd steps."""
    r, y, a = 0, 0, 0
    for j, e in enumerate(sig):
        s = (e - y) % 2
        r += s << j
        y += s * 3 ** a
        if y % 2:
            y = (3 * y + 1) // 2
            a += 1
        else:
            y //= 2
    return r, y, a


def family(rng, k, b0=3, nt=48, p=0.3, sig0=None):
    """Points of the family of the model of T (Section 6.1): x_0 = r_sigma + 2^m t, x_1 = c_sigma + 3^A t,
    x_1 = x_0 = r_{sigma_0} (mod 2^{s'})."""
    if sig0 is None:
        sig0 = [rng.random() < p for _ in range(b0)]
    blocks = list(sig0) + [rng.random() < p for _ in range(k - b0)]
    sig = [e for x in blocks for e in (BX if x else BY)]
    s0 = [e for x in sig0 for e in (BX if x else BY)]
    m, sp = len(sig), len(s0)
    r, c, A = terras(sig)
    r0, _, _ = terras(s0)
    tlow = ((r0 - c) * pow(3, -A, 1 << sp)) % (1 << sp)
    t = (1 << (nt - 1)) | (rng.getrandbits(nt - 1) & ~((1 << sp) - 1)) | tlow
    x0 = r + (t << m)
    x1 = c + 3 ** A * t
    return x0, x1, m, sp, r0


# ---------------------------------------------------------------- steps of canonical derivations (and reorderings)

def steps_fwd(s):
    """One step of T in the canonical derivation: the list of (position, rule) and the next string.
    s = '/' + bin'(n) + '.'."""
    out = []
    p = len(s) - 2
    if s[p] == "f":
        out.append((p, "f.", "."))
        s = s[:p] + "."
        return out, s
    out.append((p, "t.", "2."))
    s = s[:p] + "2."
    while s[p - 1] in "ft":
        l = s[p - 1] + s[p]
        r = "".join(AMAP[(l[0], l[1])])
        out.append((p - 1, l, r))
        s = s[:p - 1] + r + s[p + 1:]
        p -= 1
    d = s[p]
    out.append((0, "/" + d, "/" + BL[d]))
    s = "/" + BL[d] + s[2:]
    return out, s


def stack_enc(n, k):
    """The encoding E^(k)(n) = '/' d_1..d_k bits '.' (floor(n/2^L) in [3^k, 2*3^k)); k = 0 is the canonical string."""
    if k == 0:
        return "/" + binp(n) + "."
    M = 3 ** k
    L = n.bit_length() - M.bit_length()
    while L > 0 and (n >> L) < M:
        L -= 1
    while (n >> L) >= 2 * M:
        L += 1
    mval = (n >> L) - M
    dig = []
    for _ in range(k):
        dig.append(str(mval % 3))
        mval //= 3
    dig = "".join(reversed(dig))
    bits = "".join("t" if (n >> i) & 1 else "f" for i in range(L - 1, -1, -1))
    return "/" + dig + bits + "."


def steps_stack(s, k):
    """Steps from E^(k)(n) to E^(k)(T n) (k >= 1). In an odd step the new ternary digit is moved by carry rules to the
    right of the k stacked digits, the left-end rule /d_1 -> /B(d_1) is applied (B(d) = bin'(3 + d)), and then the
    bits of B(d_1) are moved to the right across the k ternary digits by carry rules in this order: first the
    rightmost bit of B(d_1), across all k digits, then the bit to its left, across all k digits (the loop below; the
    order of Section 8.2 of the paper). The sets P_E and R_E depend on this order: another order of the same carry
    steps can use other pairs at the root."""
    out = []
    p = len(s) - 2
    if s[p] == "f":
        out.append((p, "f.", "."))
        return out, s[:p] + "."
    out.append((p, "t.", "2."))
    s = s[:p] + "2."
    while s[p - 1] in "ft":
        l = s[p - 1] + s[p]
        r = "".join(AMAP[(l[0], l[1])])
        out.append((p - 1, l, r))
        s = s[:p - 1] + r + s[p + 1:]
        p -= 1
    d = s[1]
    out.append((0, "/" + d, "/" + BL[d]))
    s = "/" + BL[d] + s[2:]
    nb = len(BL[d])
    for j in range(nb, 0, -1):          # the bit at position j (j = nb, ..., 1: rightmost first) across all k digits
        q = j
        for _ in range(k):
            l = s[q] + s[q + 1]
            r = "".join(AMAP[(l[0], l[1])])
            out.append((q, l, r))
            s = s[:q] + r + s[q + 2:]
            q += 1
    return out, s


def steps_rev(s):
    """One step of T in the canonical derivation of the reversed system. s = '.' + rev(bin'(n)) + '/'."""
    out = []
    RA = {(l[1], l[0]): (r[1], r[0]) for l, r in AR}   # reversed: d b -> b' d'
    if s[1] == "f":
        out.append((0, ".f", "."))
        return out, "." + s[2:]
    out.append((0, ".t", ".2"))
    s = ".2" + s[2:]
    p = 1
    while s[p + 1] in "ft":
        l = s[p] + s[p + 1]
        r = "".join(RA[(l[0], l[1])])
        out.append((p, l, r))
        s = s[:p] + r + s[p + 2:]
        p += 1
    d = s[p]
    out.append((p, d + "/", BL[d][::-1] + "/"))
    s = s[:p] + BL[d][::-1] + "/" + s[p + 2:]
    return out, s


# ---------------------------------------------------------------- mapping chains

class Problem:
    """The dependency pair problem of a transformed system (rules, pairs, EDG, EIDG)."""

    def __init__(self, X, eidg=True):
        self.X = X
        self.R = X.rules()
        self.Rset = set(self.R)
        self.D, self.P = dps(self.R)
        self.Pidx = {p: i for i, p in enumerate(self.P)}
        self.scc = nontrivial(graph(self.P, self.D))
        self.sccof = {}
        for c, comp in enumerate(self.scc):
            for v in comp:
                self.sccof[v] = c
        self.NF = Normal(self.R)
        if eidg:
            self.iscc = nontrivial(graph(self.P, self.D, innermost=True, NF=self.NF))
            self.isccof = {}
            for c, comp in enumerate(self.iscc):
                for v in comp:
                    self.isccof[v] = c

    def walk(self, s, steps, rec):
        """Map a list of steps to the transformed system. Root steps are recorded as pairs (the pair whose right-hand
        side starts at position 0), steps below the root as rules."""
        for p, l, r in steps:
            L, Rr, q = self.X.map(s, p, l, r)
            require((L, Rr) in self.Rset, "no such rule", self.X.name, s, p, l, r)
            if q == 0:
                i = self.Pidx.get((L, Rr))
                require(i is not None, "no such pair", self.X.name, s, p, l, r)
                rec.pair(i)
            else:
                rec.rule((L, Rr))
            s = s[:p] + r + s[p + len(l):]
        return s


class Rec:
    def __init__(self):
        self.cnt = {}
        self.rules = set()
        self.edges = set()
        self.last = None

    def pair(self, i):
        self.cnt[i] = self.cnt.get(i, 0) + 1
        if self.last is not None:
            self.edges.add((self.last, i))
        self.last = i

    def rule(self, rr):
        self.rules.add(rr)

    def cut(self):
        self.last = None


class RuleCount(Rec):
    def __init__(self):
        super().__init__()
        self.rc = {}

    def rule(self, rr):
        self.rules.add(rr)
        self.rc[rr] = self.rc.get(rr, 0) + 1


def add_symbols(syms, X, s):
    """Add the symbols of the image of s under the transformation X to syms = (marked, unmarked): the root symbol is
    marked, the others are not."""
    if syms is None:
        return
    im = X.image(s)
    syms[0].add(im[0])
    syms[1].update(im[1:])


def problem_symbols(pairs, rules):
    """The symbols occurring in a set of pairs and a set of rules: (marked, unmarked). The first symbol of each side of
    a pair is marked; all other symbols of pairs and all symbols of rules are unmarked."""
    marked, unmarked = set(), set()
    for l, r in pairs:
        marked |= {l[0], r[0]}
        unmarked |= set(l[1:]) | set(r[1:])
    for l, r in rules:
        unmarked |= set(l) | set(r)
    return marked, unmarked


def run_family(pb, direction, k_stack, rng, samples, kb, syms=None):
    """Chains along the point family. Returns a Rec (all chains) and the mean number of uses per block of each
    pair. If syms = (marked, unmarked) is given, the symbols of the images of all strings along the chains are added to
    it (this uses no random numbers)."""
    tot = Rec()
    per = {}
    for _ in range(samples):
        x0, x1, m, sp, _ = family(rng, kb)
        rec = Rec()
        if direction == "fwd":
            s = stack_enc(x0, k_stack)
            for _ in range(m):
                add_symbols(syms, pb.X, s)
                st, s2 = steps_fwd(s) if k_stack == 0 else steps_stack(s, k_stack)
                s = pb.walk(s, st, rec)
                require(s == s2)
            require(s == stack_enc(x1, k_stack))
        else:
            s = "." + binp(x0)[::-1] + "/"
            for _ in range(m):
                add_symbols(syms, pb.X, s)
                st, s2 = steps_rev(s)
                s = pb.walk(s, st, rec)
                require(s == s2)
            require(s == "." + binp(x1)[::-1] + "/")
        add_symbols(syms, pb.X, s)
        for i, c in rec.cnt.items():
            per[i] = per.get(i, 0) + c / kb
            tot.cnt[i] = tot.cnt.get(i, 0) + c
        tot.rules |= rec.rules
        tot.edges |= rec.edges
    return tot, {i: v / samples for i, v in per.items()}


def redexes(R_by_first, s):
    out = []
    for p in range(len(s)):
        for l, r in R_by_first.get(s[p], ()):
            if s.startswith(l, p):
                out.append((p, l, r))
    return out


def run_innermost(pb, R, starts, max_root=400, max_steps=200000):
    """Chains built by innermost rewriting: below the root rewrite to normal form, then use a pair at the root
    (innermost steps of the transformed system)."""
    byf = {}
    for l, r in R:
        byf.setdefault(l[0], []).append((l, r))
    tot = Rec()
    for s in starts:
        tot.cut()
        nroot = 0
        for _ in range(max_steps):
            rs = redexes(byf, s)
            if not rs:
                break
            p, l, r = max(rs, key=lambda z: pb.X.tpos(s, *z))
            q = pb.X.tpos(s, p, l, r)
            if q == 0:
                L, Rr, _ = pb.X.map(s, p, l, r)
                i = pb.Pidx.get((L, Rr))
                if i is None:
                    break
                tot.pair(i)
                nroot += 1
                if nroot >= max_root:
                    break
            s = s[:p] + r + s[p + len(l):]
    return tot


def is_innermost_seq(pb, R, s, steps):
    """Whether a sequence of canonical steps is innermost (each step is a deepest redex of the transformed system)."""
    byf = {}
    for l, r in R:
        byf.setdefault(l[0], []).append((l, r))
    for p, l, r in steps:
        rs = redexes(byf, s)
        qmax = max(pb.X.tpos(s, *z) for z in rs)
        if pb.X.tpos(s, p, l, r) != qmax:
            return False
        s = s[:p] + r + s[p + len(l):]
    return True


# ---------------------------------------------------------------- dependency pair processors

def compat(a, b):
    m = min(len(a), len(b))
    return tuple(a[:m]) == tuple(b[:m])


def narrow(P, R, innermost=False, NF=None):
    """[GTSF06, Definition 28 (a)]. Full version: if the right-hand side t of a pair unifies with no left-hand side of
    P, the pair is replaced by all R-narrowings of t (possibly none); otherwise it is kept. Innermost version: a
    unifier mu with a left-hand side v only blocks if s mu and v mu are normal forms, and only narrowings with s mu in
    normal form are kept."""
    R = [(tuple(l), tuple(r)) for l, r in R]
    out = []
    for s, t in P:
        blocked = False
        for v, _ in P:
            if not (t[0] == v[0] and compat(t[1:], v[1:])):
                continue
            if not innermost:
                blocked = True
                break
            T_, V_ = t[1:], v[1:]
            smu = s[1:] + V_[len(T_):] if len(V_) > len(T_) else s[1:]
            vmu = V_ + T_[len(V_):] if len(T_) > len(V_) else V_
            if NF.ok(smu) and NF.ok(vmu):
                blocked = True
                break
        if blocked:
            out.append((s, t))
            continue
        for i in range(1, len(t)):
            sub = t[i:]
            for l, r in R:
                if not compat(sub, l):
                    continue
                if len(l) <= len(sub):
                    new = (s, t[:i] + r + t[i + len(l):])
                else:
                    new = (s + l[len(sub):], t[:i] + r)
                if innermost and not NF.ok(new[0][1:]):
                    continue
                out.append(new)
    return sorted(set(out))


def usable_symbols(R, P):
    """Usable symbols US(P, R) of [LPAR04]: the symbols of the right-hand sides of P (the root marked), and the symbols
    of the right-hand sides of rules whose first letter is usable."""
    byf = {}
    for l, r in R:
        byf.setdefault(l[0], []).append((l, r))
    US = set()
    todo = []
    for _, t in P:
        for c in [("#", t[0])] + list(t[1:]):
            if c not in US:
                US.add(c)
                todo.append(c)
    while todo:
        a = todo.pop()
        if isinstance(a, tuple):
            continue
        for _, r in byf.get(a, ()):
            for c in r:
                if c not in US:
                    US.add(c)
                    todo.append(c)
    return US


def rewritable(P, R):
    """[GTSF06, Definition 28 (b)]: pairs with a redex below the root of the right-hand side (among its letters)."""
    R = [(tuple(l), tuple(r)) for l, r in R]
    bad = []
    for s, t in P:
        for i in range(1, len(t)):
            if any(t[i:i + len(l)] == l for l, _ in R):
                bad.append((s, t))
    return bad


def instantiates(P, R, D):
    """[GTSF06, Definition 28 (c), (d)]: whether instantiation (mgu of ren(cap(w)) of a preceding pair with s) or
    forward instantiation (mgu of ren(cap^-1(v)) of a following pair with t) binds the variable of s (changes the
    pair)."""
    roots_r = {tuple(r)[0] for _, r in R}
    changed = []
    for s, t in P:
        for v, w in P:
            cw, _ = cap(w, D)
            if w[0] == s[0] and compat(cw, s[1:]) and len(cw) > len(s) - 1:
                changed.append(("inst", s, t, v, w))
        for v, w in P:
            cv = []
            for ch in v[1:]:
                if ch in roots_r:
                    break
                cv.append(ch)
            if v[0] == t[0] and compat(cv, t[1:]) and len(cv) > len(t) - 1:
                changed.append(("finst", s, t, v, w))
    return changed


class Narrowed:
    """The problem after narrowing (untransformed system, pairs from narrowing)."""

    def __init__(self, R, P):
        self.R = [(tuple(l), tuple(r)) for l, r in R]
        self.Rset = set(self.R)
        self.D = {l[0] for l, _ in self.R}
        self.P = P
        self.Pidx = {p: i for i, p in enumerate(P)}
        self.scc = nontrivial(graph(P, self.D))
        self.NF = Normal(self.R)
        self.iscc = nontrivial(graph(P, self.D, innermost=True, NF=self.NF))
        self.sccof = {v: c for c, comp in enumerate(self.scc) for v in comp}
        self.isccof = {v: c for c, comp in enumerate(self.iscc) for v in comp}

    def walk(self, s, steps, rec, root_letter):
        """A root step (the left-end rule; for the reversal `.t -> .2`) together with the following step is mapped to
        one narrowed pair."""
        j = 0
        while j < len(steps):
            p, l, r = steps[j]
            s2 = s[:p] + r + s[p + len(l):]
            if p == 0 and (root_letter == "/" or l == ".t"):
                p2, l2, r2 = steps[j + 1]
                s3 = s2[:p2] + r2 + s2[p2 + len(l2):]
                keep = len(s) - 3
                pair = (tuple(s[:3]), tuple(s3[:len(s3) - keep]))
                i = self.Pidx.get(pair)
                require(i is not None, "no narrowed pair", s, pair)
                rec.pair(i)
                s = s3
                j += 2
                continue
            if p == 0:
                i = self.Pidx.get((tuple(l), tuple(r)))
                require(i is not None, "no pair", s, l, r)
                rec.pair(i)
            else:
                require((tuple(l), tuple(r)) in self.Rset)
                rec.rule((tuple(l), tuple(r)))
            s = s2
            j += 1
        return s


def run_innermost_narrowed(nb, starts, max_root=300, max_steps=200000):
    """Innermost chains of the narrowed problem: rewrite below the root to normal form (innermost), then use a
    narrowed pair (`/#d e`) at the root."""
    byf = {}
    for l, r in nb.R:
        byf.setdefault(l[0], []).append(("".join(l), "".join(r)))
    tot = Rec()
    for s in starts:
        tot.cut()
        nroot = 0
        for _ in range(max_steps):
            rs = [z for z in redexes(byf, s) if z[0] > 0]
            if rs:
                p, l, r = max(rs)
                s = s[:p] + r + s[p + len(l):]
                continue
            hit = [j for j, (v, w) in enumerate(nb.P) if tuple(s[:len(v)]) == v]
            if not hit:
                break
            j = hit[0]
            v, w = nb.P[j]
            tot.pair(j)
            s = "".join(w) + s[len(v):]
            nroot += 1
            if nroot >= max_root:
                break
    return tot


def window_residues(L, nblk=3):
    """Residues modulo 2^L of the parity windows of length L in concatenations of X' and Y' (Terras
    correspondence)."""
    out = set()
    for mask in range(1 << nblk):
        sig = [e for j in range(nblk) for e in (BX if (mask >> j) & 1 else BY)]
        for i in range(len(sig) - L - len(BY) + 1):
            r, _, _ = terras(sig[i:i + L])
            out.add(r)
    return out


# ---------------------------------------------------------------- the checks

def stack_value(n, j):
    """The stacked value M = floor(n / 2^nu) with floor(n / 2^nu) in [3^j, 2*3^j)."""
    M = 3 ** j
    nu = max(0, n.bit_length() - M.bit_length())
    while nu > 0 and (n >> nu) < M:
        nu -= 1
    while (n >> nu) >= 2 * M:
        nu += 1
    return n >> nu


def label_is_local(pb, direction, k_stack, lo, hi):
    """Whether the sequence of pairs used at the root is a function of local data. Forward: empty in even steps; in
    odd steps a function of the first 4 letters of bin'(T(n)) (j = 0) or of the stacked value of T(n) (j >= 1).
    Reversed: a function of the lowest 4 bits of n. Returns (is a function, number of keys)."""
    seen = {}
    ok = True
    for n in range(lo, hi):
        if direction == "fwd":
            s = stack_enc(n, k_stack)
            st, _ = steps_fwd(s) if k_stack == 0 else steps_stack(s, k_stack)
            key = None
            if n % 2:
                key = binp(T(n))[:4] if k_stack == 0 else stack_value(T(n), k_stack + 1)
        else:
            s = "." + binp(n)[::-1] + "/"
            st, _ = steps_rev(s)
            key = n % 16
        roots = []

        class R2(Rec):
            def pair(self, i):
                roots.append(i)
        pb.walk(s, st, R2())
        val = tuple(roots)
        if key is None:
            ok &= not val
            continue
        if seen.setdefault(key, val) != val:
            ok = False
    return ok, len(seen)


def root_type(X, sym, letter):
    """Root-type symbols: for FC+rl the letter is the root letter; for tiling the last letter of the window."""
    return sym[0] == letter if isinstance(X, FCRL) else sym[-1] == letter


FAMW = {1, 2, 6, 9, 11}     # residues mod 16 of the parity windows of length 4 of the family


def analyse(X, direction, k_stack, rng, samples=12, kb=20, gen_hi=1 << 12):
    """P_E is defined deterministically: forward, the pairs used at the root by the steps of all n >= lo; reversed,
    the pairs used at the root by the steps of the n with n mod 16 in FAMW. R_E is the set of rules used below the
    root by the same steps. The chains of the family samples are compared with P_E and provide the edges (of actual
    chains) and the frequencies. Symbols: every symbol of the image of E(n) and of E(T(n)) for these n, and of every
    string along the family samples, must occur in P_E or R_E (the marked root symbol as a marked symbol of P_E); the
    symbols of E(n) for all n of the range that do not occur there are returned as sym_out."""
    pb = Problem(X)
    famsym = (set(), set())
    tot, per = run_family(pb, direction, k_stack, rng, samples, kb, famsym)
    Pf = set(tot.cnt)
    lo = 2 * 3 ** (k_stack + 1) + 8 if direction == "fwd" else 8
    gen = Rec()
    PE, RE = set(), set()
    defsym, allsym = (set(), set()), (set(), set())
    for n in range(lo, gen_hi):
        rec = Rec()
        if direction == "fwd":
            s = stack_enc(n, k_stack)
            st, s2 = steps_fwd(s) if k_stack == 0 else steps_stack(s, k_stack)
            require(pb.walk(s, st, rec) == s2 == stack_enc(T(n), k_stack))
        else:
            s = "." + binp(n)[::-1] + "/"
            st, s2 = steps_rev(s)
            require(pb.walk(s, st, rec) == s2 == "." + binp(T(n))[::-1] + "/")
        gen.rules |= rec.rules
        gen.cnt.update({i: gen.cnt.get(i, 0) + c for i, c in rec.cnt.items()})
        defining = direction == "fwd" or n % 16 in FAMW
        for x in (s, s2):
            add_symbols(allsym, X, x)
            if defining:
                add_symbols(defsym, X, x)
        if defining:
            PE |= set(rec.cnt)
            RE |= rec.rules
    mk, um = problem_symbols([pb.P[i] for i in PE], RE)
    sym_ok = all(sy[0] <= mk and sy[1] <= um for sy in (defsym, famsym))
    sym_out = sorted(["#" + a for a in allsym[0] - mk] + list(allsym[1] - um))
    Pg = set(gen.cnt)
    U = usable(pb.R, [pb.P[i][1] for i in PE], pb.D)
    letter = "/" if direction == "fwd" else "."
    comp_root = all(root_type(X, l[0], letter) for l, _ in set(pb.R) - U)
    gen_nonroot = all(not root_type(X, l[0], letter) for l, _ in gen.rules)
    US = usable_symbols(pb.R, [pb.P[i] for i in PE])
    us_ok = all(("#", pb.P[i][0][0]) in US and all(c in US for c in pb.P[i][0][1:]) for i in PE) and \
        all(all(c in US for c in l) for l, _ in gen.rules)
    res = {
        "rules": len(pb.R), "pairs": len(pb.P),
        "edg": (len(pb.scc), max(len(c) for c in pb.scc)), "eidg": (len(pb.iscc), max(len(c) for c in pb.iscc)),
        "P_E": len(PE), "fam_eq": Pf == PE, "sc": strongly_connected(PE, tot.edges),
        "one_edg": len({pb.sccof.get(i) for i in PE}) == 1 and None not in {pb.sccof.get(i) for i in PE},
        "one_eidg": len({pb.isccof.get(i) for i in PE}) == 1 and None not in {pb.isccof.get(i) for i in PE},
        "edg_size": len(pb.scc[pb.sccof[min(PE)]]),
        "eidg_size": len(pb.iscc[pb.isccof[min(PE)]]) if min(PE) in pb.isccof else 0,
        "U": len(U), "U_root": comp_root and gen_nonroot, "U_ok": gen.rules <= U and tot.rules <= U, "US_ok": us_ok,
        "minfreq": min(per.values()), "gen_only": sorted(Pg - PE),
        "R_E": len(RE), "RE_U": RE <= U, "sym_ok": sym_ok,
        "sym_n": len(defsym[0] | famsym[0]) + len(defsym[1] | famsym[1]), "sym_out": sym_out,
    }
    return pb, PE, tot, res


def run():
    rng = random.Random(20261004)
    RS = rev(ST)
    print("1. Sizes of the transformed systems (rules, pairs) and estimated dependency graphs ([GTSF06], Def. 9)")
    print("2. Chains along the point family: the pairs P_E used at the root, strong connectivity by observed edges,")
    print("   usable rules, frequencies, and the pairs used only by general n")
    table = {}
    keep = {}
    for direction, R in (("fwd", ST), ("rev", RS)):
        for X in (FCRL(R), Tile(R, 2), Tile(R, 3)):
            ks = (0, 2) if direction == "fwd" else (0,)
            for k in ks:
                pb, Pf, tot, res = analyse(X, direction, k, rng)
                table[(direction, X.name, k)] = res
                keep[(direction, X.name, k)] = (pb, Pf, tot)
                print(f"   {direction} {X.name:11s} E^({k}): rules {res['rules']}, pairs {res['pairs']}, "
                      f"EDG SCCs {res['edg'][0]} (largest {res['edg'][1]}), EIDG SCCs {res['eidg'][0]} "
                      f"(largest {res['eidg'][1]}), |P_E| {res['P_E']}, equal to the pairs of the family samples "
                      f"{res['fam_eq']}, strongly connected by family edges {res['sc']}, one SCC of EDG "
                      f"{res['one_edg']} (size {res['edg_size']}), one SCC of EIDG {res['one_eidg']} "
                      f"(size {res['eidg_size']}), |U(P_E)| {res['U']} (complement starts with root-type symbols, "
                      f"steps below the root do not {res['U_root']}), rules used in U(P_E) {res['U_ok']}, "
                      f"US(P_E) {res['US_ok']}, least frequency per block {res['minfreq']:.2f}, "
                      f"pairs of general n only {len(res['gen_only'])}, |R_E| {res['R_E']} (in U(P_E) {res['RE_U']}), "
                      f"the {res['sym_n']} symbols of E(n) occur in P_E or R_E {res['sym_ok']}")
    size = {key: (v["rules"], v["pairs"]) for key, v in table.items() if key[2] == 0}
    check("size", sorted(size.items()), sorted({
        ("fwd", "FC+rl", 0): (413, 496), ("fwd", "tiling w=2", 0): (539, 917), ("fwd", "tiling w=3", 0): (26411, 56252),
        ("rev", "FC+rl", 0): (455, 561), ("rev", "tiling w=2", 0): (539, 749),
        ("rev", "tiling w=3", 0): (26411, 51793)}.items()))
    check("P_E", sorted((key, v["P_E"]) for key, v in table.items()), sorted({
        ("fwd", "FC+rl", 0): 18, ("fwd", "FC+rl", 2): 27, ("fwd", "tiling w=2", 0): 6, ("fwd", "tiling w=2", 2): 9,
        ("fwd", "tiling w=3", 0): 12, ("fwd", "tiling w=3", 2): 27,
        ("rev", "FC+rl", 0): 5, ("rev", "tiling w=2", 0): 3, ("rev", "tiling w=3", 0): 4}.items()))
    ok = all(v["sc"] and v["one_edg"] and v["one_eidg"] and v["U_ok"] and v["minfreq"] > 0.05 and v["fam_eq"]
             for v in table.values())
    check("one SCC, strongly connected by observed edges, usable, positive frequency", ok, True)
    usz = sorted((key, (v["U"], v["U_root"])) for key, v in table.items() if key[2] == 0)
    check("usable rules", usz, sorted({
        ("fwd", "FC+rl", 0): (336, True), ("fwd", "tiling w=2", 0): (455, True),
        ("fwd", "tiling w=3", 0): (23912, True), ("rev", "FC+rl", 0): (378, True),
        ("rev", "tiling w=2", 0): (511, True), ("rev", "tiling w=3", 0): (26019, True)}.items()))
    check("usable symbols", all(v["US_ok"] for v in table.values()), True)
    # Theorem 8.3 (b): V_E(n) is finite if every symbol of E(n) is somewhere finite, which the reduction pair ensures
    # for the symbols of the problem; here: every symbol of E(n) (labelled or tiled, with the label of the final '.'
    # and the windows of the padding) occurs in P_E or R_E, for the n that define P_E and along the family samples
    check("symbols of E(n) occur in P_E or R_E, and R_E is contained in U(P_E)",
          all(v["sym_ok"] and v["RE_U"] for v in table.values()), True)
    print("   symbols of E(n), for any n of the range, that occur neither in P_E nor in R_E:")
    for key, v in sorted(table.items()):
        if v["sym_out"]:
            print(f"     {key}: {v['sym_out']}")
    check("symbols of E(n) outside P_E and R_E for other n", sorted((key, v["sym_out"]) for key, v in table.items()),
          sorted({("fwd", "FC+rl", 0): [], ("fwd", "FC+rl", 2): [], ("fwd", "tiling w=2", 0): [],
                  ("fwd", "tiling w=2", 2): [], ("fwd", "tiling w=3", 0): [], ("fwd", "tiling w=3", 2): [],
                  ("rev", "FC+rl", 0): [], ("rev", "tiling w=2", 0): [], ("rev", "tiling w=3", 0): [".ff"]}.items()))
    edg = sorted((key, (v["edg"][0], v["edg_size"], v["eidg"][0], v["eidg_size"]))
                 for key, v in table.items() if key[2] == 0)
    check("EDG and EIDG (number of SCCs, size of the SCC of P_E)", edg, sorted({
        ("fwd", "FC+rl", 0): (2, 69, 2, 69), ("fwd", "tiling w=2", 0): (5, 657, 8, 21),
        ("fwd", "tiling w=3", 0): (18, 46958, 34, 20534), ("rev", "FC+rl", 0): (2, 74, 2, 29),
        ("rev", "tiling w=2", 0): (3, 686, 8, 13), ("rev", "tiling w=3", 0): (5, 49911, 36, 14112)}.items()))
    rf = []
    for key, (pb, _, _) in sorted(keep.items()):
        if key[2] != 0:
            continue
        cnt = {}
        S = 12
        for _ in range(S):
            x0, _, m, _, _ = family(rng, 20)
            rec = RuleCount()
            if key[0] == "fwd":
                s = stack_enc(x0, 0)
                for _ in range(m):
                    s = pb.walk(s, steps_fwd(s)[0], rec)
            else:
                s = "." + binp(x0)[::-1] + "/"
                for _ in range(m):
                    s = pb.walk(s, steps_rev(s)[0], rec)
            for rr, c in rec.rc.items():
                cnt[rr] = cnt.get(rr, 0) + c
        rf.append(min(cnt.values()) / S / 20)
    print(f"   least number of uses per block of the rules used below the root: {', '.join(f'{v:.2f}' for v in rf)}")
    check("rules used with positive frequency", all(v > 0.05 for v in rf), True)
    gen_only = sorted((key, len(v["gen_only"])) for key, v in table.items())
    check("pairs used only by general n", gen_only, sorted({
        ("fwd", "FC+rl", 0): 0, ("fwd", "FC+rl", 2): 0, ("fwd", "tiling w=2", 0): 0, ("fwd", "tiling w=2", 2): 0,
        ("fwd", "tiling w=3", 0): 0, ("fwd", "tiling w=3", 2): 0,
        ("rev", "FC+rl", 0): 3, ("rev", "tiling w=2", 0): 1, ("rev", "tiling w=3", 0): 4}.items()))
    pb, _, _ = keep[("rev", "FC+rl", 0)]
    zero = sorted(" ".join(pb.P[i][0]) + " -> " + " ".join(pb.P[i][1]) for i in table[("rev", "FC+rl", 0)]["gen_only"])
    print("   reversed FC+rl, pairs used only by general n (parity windows that do not occur in the family):")
    for z in zero:
        print("     ", z)
    check("these pairs", zero, [".2 2f ft -> .f f1 1t", ".2 2t tt -> .t t2 2t", ".f ff -> .f"])
    W = window_residues(4)
    obs = set()
    for _ in range(20):
        x0, _, m, _, _ = family(rng, 20)
        x = x0
        for _ in range(m + 1):
            obs.add(x % 16)
            x = T(x)
    print(f"   residues mod 16 of the family points {sorted(obs)}, of the windows of length 4 of X'Y' {sorted(W)}")
    check("window residues", (sorted(obs), obs == W), ([1, 2, 6, 9, 11], True))
    loc = {key: label_is_local(keep[key][0], key[0], key[2], 2 ** 9, 2 ** 13) for key in keep}
    print("   the pairs used at the root are a function of the first 4 letters of bin'(T(n)) (forward, j = 0), of the "
          "stacked value (forward, j = 2), and of n mod 16 (reversed); (function, number of keys):")
    for key, v in sorted(loc.items()):
        print(f"     {key}: {v}")
    check("locality", sorted((k, v) for k, v in loc.items()), sorted({
        ("fwd", "FC+rl", 0): (True, 16), ("fwd", "FC+rl", 2): (True, 27), ("fwd", "tiling w=2", 0): (True, 16),
        ("fwd", "tiling w=2", 2): (True, 27), ("fwd", "tiling w=3", 0): (True, 16), ("fwd", "tiling w=3", 2): (True, 27),
        ("rev", "FC+rl", 0): (True, 16), ("rev", "tiling w=2", 0): (True, 16),
        ("rev", "tiling w=3", 0): (True, 16)}.items()))
    # the uses in the reversal are deterministic: of the windows of length 4, 1011, 0110, 1101 occur inside every
    # block and 1010, 0101 at every junction
    wstr = lambda sig, i: "".join(str(e) for e in sig[i:i + 4])  # noqa: E731
    inner = all({"1011", "0110", "1101"} <= {wstr(b, i) for i in range(len(b) - 3)} for b in (BX, BY))
    joint = all({"1010", "0101"} <= {wstr(b1 + b2, i) for i in range(len(b1) - 3, len(b1))}
                for b1 in (BX, BY) for b2 in (BX, BY))
    wres = {terras([int(c) for c in w])[0] for w in ("1011", "0110", "1101", "1010", "0101")}
    cnt_ok = True
    for _ in range(12):
        x0, _, m, _, _ = family(rng, 20)
        cnt = {}
        x = x0
        for _ in range(m):
            cnt[x % 16] = cnt.get(x % 16, 0) + 1
            x = T(x)
        cnt_ok &= all(cnt.get(r, 0) >= 20 - 1 for r in FAMW)
    print(f"   windows 1011, 0110, 1101 inside every block {inner}, 1010, 0101 at every junction {joint}, residues of "
          f"the five windows {sorted(wres)}, each residue at least k - 1 times in the family samples {cnt_ok}")
    check("reversed uses", (inner, joint, sorted(wres), cnt_ok), (True, True, [1, 2, 6, 9, 11], True))

    print("3. Innermost chains (edges of chains built by innermost rewriting of T)")
    res3 = {}
    pbI = Problem(Ident(ST), eidg=False)
    keep[("fwd", "none", 0)] = (pbI, {pbI.Pidx[p] for p in pbI.P if p[0][0] == "/" and p[1][0] == "/"}, None)
    keep[("fwd", "none", 2)] = keep[("fwd", "none", 0)]
    for X in (Ident(ST), FCRL(ST), Tile(ST, 2), Tile(ST, 3)):
        pb, P0, _ = keep[("fwd", X.name, 0)]
        _, P2, _ = keep[("fwd", X.name, 2)]
        starts = ["/" + binp(rng.getrandbits(36) | (1 << 35)) + "." for _ in range(12)]
        inn = run_innermost(pb, list(ST), starts, max_root=250)
        Pi = set(inn.cnt)
        sub = {(a, b) for a, b in inn.edges if a in P2 and b in P2}
        res3[X.name] = (len(P0 & Pi), P2 <= Pi, strongly_connected(P2, sub))
        print(f"   {X.name}: pairs of the canonical encoding E^(0) in innermost chains {len(P0 & Pi)}/{len(P0)}, "
              f"all pairs of E^(2) occur {P2 <= Pi}, strongly connected by innermost edges among them "
              f"{strongly_connected(P2, sub)}")
    check("innermost chains", sorted(res3.items()), sorted({
        "none": (3, True, True), "FC+rl": (0, True, True), "tiling w=2": (0, True, True),
        "tiling w=3": (0, True, True)}.items()))
    innrev = True
    keep[("rev", "none", 0)] = (Problem(Ident(RS), eidg=False), None, None)
    for X in (Ident(RS), FCRL(RS), Tile(RS, 2), Tile(RS, 3)):
        pb = keep[("rev", X.name, 0)][0]
        for n in range(8, 400):
            s = "." + binp(n)[::-1] + "/"
            innrev &= is_innermost_seq(pb, list(RS), s, steps_rev(s)[0])
    print(f"   the canonical derivations of the reversal are innermost, untransformed and after the three "
          f"transformations: {innrev}")
    check("reversed derivations innermost", innrev, True)

    print("4. Dependency pair processors: rewriting, instantiation, narrowing (P_B and P_T^rev)")
    out4 = {}
    for direction, R, letter in (("fwd", ST, "/"), ("rev", RS, ".")):
        pb0 = Problem(Ident(R), eidg=False)
        core = [p for p in pb0.P if p[0][0] == letter and p[1][0] == letter]
        rw = rewritable(core, R)
        ins = instantiates(core, R, pb0.D)
        PN = narrow(core, R)
        PNi = narrow(core, R, innermost=True, NF=Normal([(tuple(l), tuple(r)) for l, r in R]))
        require(PNi == PN, "the innermost narrowing differs from the full one")
        nb = Narrowed(R, PN)
        tot = Rec()
        per = {}
        for _ in range(12):
            x0, x1, m, _, _ = family(rng, 20)
            rec = Rec()
            if direction == "fwd":
                s = stack_enc(x0, 1)
                for _ in range(m):
                    st, s2 = steps_stack(s, 1)
                    s = nb.walk(s, st, rec, "/")
                    require(s == s2)
            else:
                s = "." + binp(x0)[::-1] + "/"
                for _ in range(m):
                    st, s2 = steps_rev(s)
                    s = nb.walk(s, st, rec, ".")
                    require(s == s2)
            for i, c in rec.cnt.items():
                per[i] = per.get(i, 0) + c / 20 / 12
            tot.edges |= rec.edges
            tot.rules |= rec.rules
            tot.cnt.update({i: tot.cnt.get(i, 0) + c for i, c in rec.cnt.items()})
        Pf = set(tot.cnt)
        U = usable(nb.R, [nb.P[i][1] for i in Pf], nb.D)
        sc = strongly_connected(Pf, tot.edges)
        if direction == "fwd":
            starts = ["/" + binp(rng.getrandbits(36) | (1 << 35)) + "." for _ in range(12)]
        else:
            starts = ["." + binp(rng.getrandbits(36) | (1 << 35))[::-1] + "/" for _ in range(12)]
        inn = run_innermost_narrowed(nb, starts)
        sub = {(a, b) for a, b in inn.edges if a in Pf and b in Pf}
        isc = strongly_connected(Pf, sub)
        unused = sorted("".join(nb.P[i][0]) + "->" + "".join(nb.P[i][1]) for i in range(len(nb.P)) if i not in Pf)
        out4[direction] = (len(rw), len(ins), len(PN), len(Pf), sc, isc, tot.rules <= U, min(per.values()) > 0.05,
                           unused)
        print(f"   {direction}: pairs changed by rewriting {len(rw)}, by instantiation {len(ins)}, pairs after "
              f"narrowing {len(PN)}, used by the family {len(Pf)} (strongly connected {sc}, by innermost edges "
              f"{isc}, usable {tot.rules <= U}, least frequency per block {min(per.values()):.2f}), not used by the "
              f"family {unused}")
    check("processors", sorted(out4.items()), sorted({
        "fwd": (0, 0, 12, 9, True, True, True, True, ["/0.->/2.", "/1.->/f.", "/2.->/f2."]),
        "rev": (0, 0, 4, 3, True, True, True, True, [".t/->.tf/"])}.items()))


def main():
    try:
        run()
    except CheckFailed as e:
        print(f"FAILED: {e}")
        return 1
    print("ALL OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
