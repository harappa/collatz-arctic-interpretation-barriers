#!/usr/bin/env python3
"""Certificates for Theorem 8.3 (Section 8.2 of the paper, Appendix C). Python 3, standard library only.

    python3 computations/export_certificates.py            (regenerate and compare with computations/certificates)
    python3 computations/export_certificates.py --write    (write the files)

This is the generating side. It uses check_transforms.py to build the transformed systems and the chains, and writes,
for T with the encoding E^(2) and for the reversal T^rev with E^(0), for root labelling (after flat context closure)
and for full tiling of widths 2 and 3, and for full and for innermost chains, one JSON file with
- the pairs of P_E (each a pair of lists of transformed symbols; the first symbol of each side is the marked root);
- for every edge between two pairs of P_E used by the witness chains, one witness: a string of collatz-T (or of its
  reversal) and the list of rewrite steps (position, left side, right side) of that system, starting with the step
  whose image is a root step by the first pair, ending with the step whose image is a root step by the second pair,
  with only steps below the root in between;
- the locality table: for each value of M (T) or of n mod 16 (T^rev), the sequence of pairs (as symbol lists) used
  at the root in one step of T, with one string E(n) that realizes it.
The certificates are checked by check_certificates.py, a separate program that does not import this file or
check_transforms.py. The edges recorded here are the edges of actual chains; the checker recomputes the transformed
rules, the dependency pairs, the root and innermost conditions and the strong connectivity on its own.
"""
import json
import os
import random
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
import check_transforms as ct  # noqa: E402  (the directory of this script is on the import path)


def pe_set(pb, direction, k):
    """P_E as defined in Section 8.2 (and in check_transforms.analyse)."""
    lo = 2 * 3 ** (k + 1) + 8 if direction == "fwd" else 8
    PE = set()
    for n in range(lo, 1 << 12):
        if direction == "rev" and n % 16 not in ct.FAMW:
            continue
        rec = ct.Rec()
        if direction == "fwd":
            s = ct.stack_enc(n, k)
            pb.walk(s, ct.steps_stack(s, k)[0], rec)
        else:
            s = "." + ct.binp(n)[::-1] + "/"
            pb.walk(s, ct.steps_rev(s)[0], rec)
        PE |= set(rec.cnt)
    return PE


class Recorder:
    """Walks steps one by one and keeps, for each new edge (a, b), the steps from the root step by a to the root step
    by b."""

    def __init__(self, pb):
        self.pb = pb
        self.wit = {}
        self.cur = None          # (start string, [steps]) since the last root step
        self.last = None

    def cut(self):
        self.cur, self.last = None, None

    def step(self, s, p, l, r):
        """s: the string before the step. Returns the string after it and the pair index or None."""
        L, Rr, q = self.pb.X.map(s, p, l, r)
        ct.require((L, Rr) in self.pb.Rset, "no such rule", s, p, l, r)
        i = self.pb.Pidx.get((L, Rr)) if q == 0 else None
        if q == 0:
            ct.require(i is not None, "no such pair", s, p, l, r)
        if self.cur is not None:
            self.cur[1].append([p, l, r])
        if i is not None:
            if self.last is not None and (self.last, i) not in self.wit:
                self.wit[(self.last, i)] = {"start": self.cur[0], "steps": list(self.cur[1])}
            self.cur, self.last = (s, [[p, l, r]]), i
        return s[:p] + r + s[p + len(l):]


def sym_list(t):
    return [str(x) if isinstance(x, str) else "".join(x) for x in t]


def family_witnesses(pb, direction, k, rng, samples=12, kb=20):
    rc = Recorder(pb)
    for _ in range(samples):
        x0, x1, m, _, _ = ct.family(rng, kb)
        rc.cut()
        if direction == "fwd":
            s = ct.stack_enc(x0, k)
            for _ in range(m):
                st, s2 = ct.steps_stack(s, k)
                for p, l, r in st:
                    s = rc.step(s, p, l, r)
                ct.require(s == s2)
        else:
            s = "." + ct.binp(x0)[::-1] + "/"
            for _ in range(m):
                st, s2 = ct.steps_rev(s)
                for p, l, r in st:
                    s = rc.step(s, p, l, r)
                ct.require(s == s2)
    return rc.wit


def innermost_witnesses(pb, rng, starts_n=12, max_root=250, max_steps=200000):
    """As check_transforms.run_innermost, recording witnesses: below the root rewrite to normal form (deepest redex
    of collatz-T first), then a pair at the root."""
    byf = {}
    for l, r in ct.ST:
        byf.setdefault(l[0], []).append((l, r))
    rc = Recorder(pb)
    for _ in range(starts_n):
        s = "/" + ct.binp(rng.getrandbits(36) | (1 << 35)) + "."
        rc.cut()
        nroot = 0
        for _ in range(max_steps):
            rs = ct.redexes(byf, s)
            if not rs:
                break
            p, l, r = max(rs, key=lambda z: pb.X.tpos(s, *z))
            if pb.X.tpos(s, p, l, r) == 0:
                L, Rr, _ = pb.X.map(s, p, l, r)
                if pb.Pidx.get((L, Rr)) is None:
                    break
                nroot += 1
                if nroot > max_root:
                    break
            s = rc.step(s, p, l, r)
    return rc.wit


def locality(pb, direction, k, rng):
    """For each key (M for T, n mod 16 for T^rev), the sequence of pairs used at the root in the step from n, with
    the string E(n)."""
    out = {}
    tries = 0
    want = 27 if direction == "fwd" else 16
    while len(out) < want and tries < 200000:
        tries += 1
        n = rng.randrange(1 << 20, 1 << 40)
        if direction == "fwd":
            if n % 2 == 0:
                continue
            key = ct.stack_value(ct.T(n), k + 1)
            s = ct.stack_enc(n, k)
            st, _ = ct.steps_stack(s, k)
        else:
            key = n % 16
            s = "." + ct.binp(n)[::-1] + "/"
            st, _ = ct.steps_rev(s)
        seq = []
        t = s
        for p, l, r in st:
            L, Rr, q = pb.X.map(t, p, l, r)
            if q == 0:
                seq.append(pb.Pidx[(L, Rr)])
            t = t[:p] + r + t[p + len(l):]
        if key in out:
            ct.require(out[key][0] == seq, "not local", key)
        else:
            out[key] = (seq, s)
    ct.require(len(out) == want)
    return out


def strongly_connected(nodes, edges):
    return ct.strongly_connected(set(nodes), set(edges))


def main():
    write = "--write" in sys.argv
    outdir = os.path.join(HERE, "certificates")
    if write:
        os.makedirs(outdir, exist_ok=True)
    rng = random.Random(20261014)
    RS = ct.rev(ct.ST)
    count = 0
    for direction, R, k, sysname, enc in (("fwd", ct.ST, 2, "T", "E2"), ("rev", RS, 0, "Trev", "E0")):
        for X, tname in ((ct.FCRL(R), "rootlabel"), (ct.Tile(R, 2), "tile2"), (ct.Tile(R, 3), "tile3")):
            pb = ct.Problem(X, eidg=False)
            PE = sorted(pe_set(pb, direction, k))
            loc = locality(pb, direction, k, rng)
            for kind in ("full", "innermost"):
                if direction == "fwd" and kind == "innermost":
                    wit = innermost_witnesses(pb, rng)
                else:
                    wit = family_witnesses(pb, direction, k, rng)
                edges = {e: w for e, w in wit.items() if e[0] in PE and e[1] in PE}
                ct.require(strongly_connected(PE, edges), "not strongly connected", sysname, tname, kind)
                idx = {i: j for j, i in enumerate(PE)}
                cert = {
                    "system": sysname, "transformation": tname, "encoding": enc, "chains": kind,
                    "pairs": [[sym_list(pb.P[i][0]), sym_list(pb.P[i][1])] for i in PE],
                    "witnesses": [{"edge": [idx[a], idx[b]], "start": w["start"], "steps": w["steps"]}
                                  for (a, b), w in sorted(edges.items())],
                    "locality": [{"key": key, "pairs": [[sym_list(pb.P[i][0]), sym_list(pb.P[i][1])] for i in seq],
                                  "start": st} for key, (seq, st) in sorted(loc.items())],
                }
                name = f"{sysname}-{tname}-{kind}.json"
                text = json.dumps(cert, separators=(",", ":")) + "\n"
                path = os.path.join(outdir, name)
                if write:
                    with open(path, "w") as fh:
                        fh.write(text)
                else:
                    with open(path) as fh:
                        ct.require(fh.read() == text, "the certificate differs from the regenerated one", name)
                count += 1
                nsteps = sum(len(w["steps"]) for w in cert["witnesses"])
                print(f"{name}: |P_E| {len(PE)}, witnessed edges {len(cert['witnesses'])}, steps {nsteps}, "
                      f"locality keys {len(cert['locality'])}" + ("" if write else ", reproduced byte for byte"),
                      flush=True)
    ct.require(count == 12)
    print("ALL OK")


if __name__ == "__main__":
    main()
