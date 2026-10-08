/* Question 4.4 of the paper (the rules L0 -> L and Lf -> L of R_H and condition (CF); a numerical observation):
   an exhaustive search for arctic interpretations of dimension 2 that weakly orient the ten used rules of R_H,
   strictly orient L0 -> L or Lf -> L, and satisfy condition (CF).
   A solution would show that the bound of Theorem 3.1 (ii) (only the remaining rules L0 -> L and Lf -> L can be
   strictly oriented) is attained by an interpretation with (CF), since it weakly orients the used rules together
   with that rule. Finding none only supports the expectation that this does not happen under (CF); it is not a
   proof (dimension 2 and entries at most K only).

   Originally the search of an independent internal reviewer (one program and three variants), combined into one
   program with the variants as modes.
   * Entries are in {-inf, 0, 1, ..., K}; the entry (0,0) of every letter is finite (Fin00). Products are max-plus.
   * Weak orientation [l] >= [r]: wherever the entry of r is finite, that of l is finite and >=. Strict orientation
     [l] >> [r]: in every entry, both are -inf, or l is finite and greater than r (r may be -inf). As in Definition
     2.1 of the paper and in `Weak`, `Strict` of the Lean sources.
   * (CF) (the form for R_H): with I the set of indices reachable from the support of the 0-th column of c = M_.
     along finite entries of N_f = M_f and N_t = M_t (s in I and N_b[i][s] finite imply i in I), every column of N_f
     and N_t indexed by I has exactly one finite entry, and the 0-th row u of M_L is finite on I. Since M_.(0,0) is
     finite, the index 0 is in I, and since M_f(0,0) and M_t(0,0) are finite, under (CF) the 0-th columns of M_f and
     M_t have no finite entry other than (0,0) (used to prune the search).
   * Modes:
       cf     (CF) itself (default).
       cfnou  (CF) without "u is finite on I".
       col0   (CF) weakened to "the 0-th columns of M_f and M_t are finite only at (0,0)" (a necessary condition
              for (CF)).
       none   control: without (CF) (checks that interpretations of the type of ILeft are found).
   * Rules (R_H): the six carry rules f0->0f, f1->0t, f2->1f, t0->1t, t1->2f, t2->2t, the used left-end rules
     L1->Lt, L2->Ltf, and the dynamic rules ff.->0., ttt.->22. L0->L and Lf->L need not be weakly oriented; one of
     them must be strictly oriented.
   * No large powers occur (values are sums of small integers at most K). Memory: a few tens of kilobytes. One
     process, one thread.

   Compile and run (from the root of the release; the executable may be placed anywhere):
       gcc -O2 -o rh_cf_search computations/rh_cf_search.c
       ./rh_cf_search 1 cf      # entries at most 1, under a second
       ./rh_cf_search 2 cf      # entries at most 2, about 1.5 minutes
       ./rh_cf_search 1 none    # control (34820 interpretations)
   K = 3 takes hours.
   Output: the first 5 solutions (if any), the number of tuples that satisfy the carry rules, the number of
   solutions found, and whether ILeft is among them. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NI (-100000)
#define D 2
#define MAXM 4096

typedef struct { int a[D][D]; } M;

static M mul(M x, M y) {
  M z;
  for (int i = 0; i < D; i++)
    for (int j = 0; j < D; j++) {
      int b = NI;
      for (int k = 0; k < D; k++) {
        if (x.a[i][k] <= NI / 2 || y.a[k][j] <= NI / 2) continue;
        int v = x.a[i][k] + y.a[k][j];
        if (v > b) b = v;
      }
      z.a[i][j] = b;
    }
  return z;
}

static int fin(int v) { return v > NI / 2; }

/* Weak orientation [l] >= [r]. */
static int ge(M l, M r) {
  for (int i = 0; i < D; i++)
    for (int j = 0; j < D; j++) {
      if (!fin(r.a[i][j])) continue;
      if (!fin(l.a[i][j]) || l.a[i][j] < r.a[i][j]) return 0;
    }
  return 1;
}

/* Strict orientation [l] >> [r]. */
static int gg(M l, M r) {
  for (int i = 0; i < D; i++)
    for (int j = 0; j < D; j++) {
      int fl = fin(l.a[i][j]), fr = fin(r.a[i][j]);
      if (!fl && !fr) continue;
      if (!fl) return 0;
      if (fr && l.a[i][j] <= r.a[i][j]) return 0;
    }
  return 1;
}

/* (CF). With need_u = 0, the condition "u is finite on I" is dropped. */
static int cf(M mf, M mt, M ml, M md, int need_u) {
  int in[D] = {0};
  for (int j = 0; j < D; j++)
    if (fin(md.a[j][0])) in[j] = 1;
  int ch = 1;
  while (ch) {
    ch = 0;
    for (int s = 0; s < D; s++)
      if (in[s])
        for (int i = 0; i < D; i++)
          if (!in[i] && (fin(mf.a[i][s]) || fin(mt.a[i][s]))) { in[i] = 1; ch = 1; }
  }
  for (int j = 0; j < D; j++)
    if (in[j]) {
      int c1 = 0, c2 = 0;
      for (int i = 0; i < D; i++) { c1 += fin(mf.a[i][j]); c2 += fin(mt.a[i][j]); }
      if (c1 != 1 || c2 != 1) return 0;
      if (need_u && !fin(ml.a[0][j])) return 0;
    }
  return 1;
}

static M all[MAXM], ftset[MAXM];

/* Control: ILeft of RH/NonVacuity.lean (f and 0 are [[0,-inf],[1,1]], L is [[0,0],[-inf,-inf]], the others
   [[0,-inf],[0,-inf]]). */
static int is_ileft(M mf, M mt, M m0, M m1, M m2, M ml, M md) {
  const M FZ = {{{0, NI}, {1, 1}}}, OT = {{{0, NI}, {0, NI}}}, LL = {{{0, 0}, {NI, NI}}};
  M got[7] = {mf, mt, m0, m1, m2, ml, md}, want[7] = {FZ, OT, FZ, OT, OT, LL, OT};
  for (int q = 0; q < 7; q++)
    for (int i = 0; i < D; i++)
      for (int j = 0; j < D; j++) {
        int x = got[q].a[i][j], y = want[q].a[i][j];
        if (fin(x) != fin(y) || (fin(x) && x != y)) return 0;
      }
  return 1;
}
static int nall = 0, nft = 0;

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: rh_cf_search <K> [cf|cfnou|col0|none]\n"); return 1; }
  int K = atoi(argv[1]);
  const char *mode = argc > 2 ? argv[2] : "cf";
  int m_cf = !strcmp(mode, "cf"), m_cfnou = !strcmp(mode, "cfnou"), m_col0 = !strcmp(mode, "col0"),
      m_none = !strcmp(mode, "none");
  if (!(m_cf || m_cfnou || m_col0 || m_none)) { fprintf(stderr, "the mode must be cf, cfnou, col0 or none\n"); return 1; }
  if (K < 0 || K > 6) { fprintf(stderr, "K must be 0 to 6 (the number (K+1)(K+2)^3 of matrices must be at most %d)\n", MAXM); return 1; }
  int V = K + 2; /* index of a value: 0 is -inf, 1..K+1 are 0..K */
  int vals[16];
  vals[0] = NI;
  for (int v = 0; v <= K; v++) vals[v + 1] = v;
  for (int c0 = 1; c0 < V; c0++)
    for (int c1 = 0; c1 < V; c1++)
      for (int c2 = 0; c2 < V; c2++)
        for (int c3 = 0; c3 < V; c3++) {
          M m;
          m.a[0][0] = vals[c0]; m.a[0][1] = vals[c1]; m.a[1][0] = vals[c2]; m.a[1][1] = vals[c3];
          all[nall++] = m;
          /* Under (CF) and its weakened forms the 0-th columns of M_f and M_t are finite only at (0,0) (c2 is -inf). No
             restriction in the control mode. */
          if (c2 == 0 || m_none) ftset[nft++] = m;
        }
  long found = 0, cnt1 = 0;
  int ileft_seen = 0;
  for (int a = 0; a < nft; a++) {
    M mf = ftset[a];
    for (int b = 0; b < nft; b++) {
      M mt = ftset[b];
      for (int c = 0; c < nall; c++) {
        M m0 = all[c];
        if (!ge(mul(mf, m0), mul(m0, mf))) continue;           /* f0 -> 0f */
        for (int e = 0; e < nall; e++) {
          M m2 = all[e];
          if (!ge(mul(mt, m2), mul(m2, mt))) continue;         /* t2 -> 2t */
          M ff = mul(mf, mf), ttt = mul(mt, mul(mt, mt)), m22 = mul(m2, m2);
          for (int g = 0; g < nall; g++) {
            M m1 = all[g];
            if (!ge(mul(mf, m1), mul(m0, mt))) continue;       /* f1 -> 0t */
            if (!ge(mul(mf, m2), mul(m1, mf))) continue;       /* f2 -> 1f */
            if (!ge(mul(mt, m0), mul(m1, mt))) continue;       /* t0 -> 1t */
            if (!ge(mul(mt, m1), mul(m2, mf))) continue;       /* t1 -> 2f */
            cnt1++;
            for (int h = 0; h < nall; h++) {
              M ml = all[h];
              if (!ge(mul(ml, m1), mul(ml, mt))) continue;          /* L1 -> Lt */
              if (!ge(mul(ml, m2), mul(ml, mul(mt, mf)))) continue; /* L2 -> Ltf */
              int s0 = gg(mul(ml, m0), ml), sf = gg(mul(ml, mf), ml); /* strictly orient L0 -> L or Lf -> L */
              if (!s0 && !sf) continue;
              for (int k = 0; k < nall; k++) {
                M md = all[k];
                if (!ge(mul(ff, md), mul(m0, md))) continue;    /* ff. -> 0. */
                if (!ge(mul(ttt, md), mul(m22, md))) continue;  /* ttt. -> 22. */
                if (m_cf && !cf(mf, mt, ml, md, 1)) continue;
                if (m_cfnou && !cf(mf, mt, ml, md, 0)) continue;
                found++;
                ileft_seen |= is_ileft(mf, mt, m0, m1, m2, ml, md);
                if (found <= 5) {
                  printf("FOUND s0=%d sf=%d\n", s0, sf);
                  M ms[7] = {mf, mt, m0, m1, m2, ml, md};
                  const char *nm[7] = {"f", "t", "0", "1", "2", "L", "."};
                  for (int q = 0; q < 7; q++)
                    printf(" %s: [[%d,%d],[%d,%d]]\n", nm[q], ms[q].a[0][0], ms[q].a[0][1], ms[q].a[1][0],
                           ms[q].a[1][1]);
                }
              }
            }
          }
        }
      }
    }
  }
  printf("K=%d mode=%s nall=%d nft=%d A-survivors=%ld found=%ld ILeft=%d (-100000 in the output is -inf)\n", K, mode, nall,
         nft, cnt1, found, ileft_seen);
  return 0;
}
