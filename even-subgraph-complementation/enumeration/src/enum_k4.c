// Independent recount of Section 4 of the paper.
// Enumerate multisets of n non-zero vectors of F_2^4 that span F_2^4; graph: i~j iff omega(u_i,u_j)=1,
// omega the standard symplectic form. Decide 4-rigidity (rank A = 4 and rank(A+D) > 4 for all D != 0)
// by testing diagonals; by twin symmetry a diagonal is determined, up to an automorphism, by how many
// vertices of each twin class (equal vector) it hits, so we test those counts. Supports |T| > 8 are
// skipped since rank(A+D) >= rank D - rank A = |T| - 4 > 4.  (This is the only reduction used.)
// Minimal forbidden (for c2<=4, among rank-4 graphs) := 4-rigid and no vertex-deleted subgraph 4-rigid.
// Usage: enum_k4 n [part parts]
// Compiled with -DPRUNE it also skips diagonals with |T| > 2d, d = 4 - dim span(rows outside T); this uses
// the inequality rank(A+D) >= |T| + k - 2d (consequence of Lemma 2 of the paper, checked by
// hand and on random instances). The unpruned build is fully independent of the paper.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned int u32;
static int om(int x, int y) {
  int a = ((x & 1) & ((y >> 1) & 1)) ^ (((x >> 1) & 1) & (y & 1));
  int b = (((x >> 2) & 1) & ((y >> 3) & 1)) ^ (((x >> 3) & 1) & ((y >> 2) & 1));
  return a ^ b;
}
static int OM[16][16];
static int rankbits(u32 *r, int n) {
  u32 m[32]; memcpy(m, r, n * sizeof(u32));
  int rk = 0;
  for (int c = 0; c < n && rk < n; c++) {
    u32 bit = 1u << c; int p = -1;
    for (int i = rk; i < n; i++) if (m[i] & bit) { p = i; break; }
    if (p < 0) continue;
    u32 t = m[p]; m[p] = m[rk]; m[rk] = t;
    for (int i = 0; i < n; i++) if (i != rk && (m[i] & bit)) m[i] ^= m[rk];
    rk++;
  }
  return rk;
}
static int spanrank(const int *v, int n) {
  int b[4] = {0}, rk = 0;
  for (int i = 0; i < n; i++) { int x = v[i];
    for (int j = 0; j < rk; j++) if ((x ^ b[j]) < x) x ^= b[j];
    if (x) { b[rk++] = x; // keep reduced: sort desc by leading bit
      for (int a = rk - 1; a > 0 && b[a] > b[a-1]; a--) { int t = b[a]; b[a] = b[a-1]; b[a-1] = t; } }
  }
  return rk;
}
// try all partial hits (0..mult-1 per class not in F), extra total <= budget; return 1 if some T!=0 gives rank<=4
static int partial(u32 *r, int n, int nc, int *start, int *mult, u32 F, int b, int budget, int tot) {
  if (b == nc) return tot >= 1 && rankbits(r, n) <= 4;
  if (F >> b & 1) return partial(r, n, nc, start, mult, F, b + 1, budget, tot);
  for (int cb = 0; cb < mult[b] && cb <= budget; cb++) {
    if (cb > 0) { int i = start[b] + cb - 1; r[i] ^= 1u << i; }
    int res = partial(r, n, nc, start, mult, F, b + 1, budget - cb, tot + cb);
    if (res) { for (int t = 0; t < cb; t++) { int i = start[b] + t; r[i] ^= 1u << i; } return 1; }
  }
  { int cmax = mult[b] - 1 < budget ? mult[b] - 1 : budget;
    for (int t = 0; t < cmax; t++) { int i = start[b] + t; r[i] ^= 1u << i; } }
  return 0;
}
// is the multiset v[0..n-1] (sorted) 4-rigid?
static int rigid(const int *v, int n) {
  if (spanrank(v, n) != 4) return 0;
  u32 rows[32];
  for (int i = 0; i < n; i++) { rows[i] = 0; for (int j = 0; j < n; j++) if (OM[v[i]][v[j]]) rows[i] |= 1u << j; }
  // twin classes: consecutive equal entries
  int start[32], mult[32], nc = 0;
  for (int i = 0; i < n; ) { int j = i; while (j < n && v[j] == v[i]) j++; start[nc] = i; mult[nc] = j - i; nc++; i = j; }
#ifdef FAST
  // T != 0 with rank(A+D) <= 4 forces d >= 1, so the rows outside the fully-hit classes F lie in a hyperplane H:
  // F contains every class whose vector is outside H. Enumerate H (15 choices), then F within H.
  for (int h = 1; h < 16; h++) {
    u32 F0 = 0; int inH[32], ni = 0;
    for (int b = 0; b < nc; b++) { if (__builtin_popcount(h & v[start[b]]) & 1) F0 |= 1u << b; else inH[ni++] = b; }
    int sf0 = 0; for (int b = 0; b < nc; b++) if (F0 >> b & 1) sf0 += mult[b];
    if (sf0 > 8) continue;
    for (u32 s1 = 0; s1 < (1u << ni); s1++) {
      u32 F = F0; for (int t = 0; t < ni; t++) if (s1 >> t & 1) F |= 1u << inH[t];
      int sf = 0; for (int b = 0; b < nc; b++) if (F >> b & 1) sf += mult[b];
      if (sf > 8) continue;
      int w[32], m = 0; for (int b = 0; b < nc; b++) if (!(F >> b & 1)) w[m++] = v[start[b]];
      int d = 4 - spanrank(w, m);
      if (sf > 2 * d) continue;
      u32 r2[32]; memcpy(r2, rows, n * sizeof(u32));
      for (int b = 0; b < nc; b++) if (F >> b & 1) for (int t = 0; t < mult[b]; t++) { int i = start[b] + t; r2[i] ^= 1u << i; }
      if (partial(r2, n, nc, start, mult, F, 0, 2 * d - sf, sf)) return 0;
    }
  }
  return 1;
#endif
  int c[32]; memset(c, 0, sizeof c);
  while (1) {
    int a = 0; while (a < nc && c[a] == mult[a]) { c[a] = 0; a++; }
    if (a == nc) break; c[a]++;
    int tot = 0; for (int b = 0; b < nc; b++) tot += c[b];
    if (tot > 8) continue;
#ifdef PRUNE
    { int w[32], m = 0; for (int b = 0; b < nc; b++) if (c[b] < mult[b]) w[m++] = v[start[b]];
      int d = 4 - spanrank(w, m); if (tot > 2 * d) continue; }
#endif
    u32 r2[32]; memcpy(r2, rows, n * sizeof(u32));
    for (int b = 0; b < nc; b++) for (int t = 0; t < c[b]; t++) { int i = start[b] + t; r2[i] ^= 1u << i; }
    if (rankbits(r2, n) <= 4) return 0;
  }
  return 1;
}
static long long cnt_min = 0, cnt_rigid = 0, cnt_all = 0;
static long long size_hist[32];
static int N, PART, PARTS; static long long leafno = 0;
static void rec(int *v, int pos, int minval) {
  if (pos == N) {
    leafno++;
    if (PARTS > 1 && (leafno % PARTS) != PART) return;
    cnt_all++;
    if (!rigid(v, N)) return;
    cnt_rigid++;
    int w[32];
    for (int i = 0; i < N; i++) {
      if (i > 0 && v[i] == v[i-1]) continue;
      int m = 0; for (int j = 0; j < N; j++) if (j != i) w[m++] = v[j];
      if (rigid(w, N - 1)) return;
    }
    cnt_min++;
#ifdef PRINT
    for (int i = 0; i < N; i++) printf("%d ", v[i]); printf("\n");
#endif
    return;
  }
  for (int x = minval; x <= 15; x++) { v[pos] = x; rec(v, pos + 1, x); }
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); PART = argc > 2 ? atoi(argv[2]) : 0; PARTS = argc > 3 ? atoi(argv[3]) : 1;
  for (int x = 0; x < 16; x++) for (int y = 0; y < 16; y++) OM[x][y] = om(x, y);
  int v[32]; rec(v, 0, 1);
  printf("n=%d part=%d/%d multisets=%lld rigid=%lld minimal_forbidden=%lld\n", N, PART, PARTS, cnt_all, cnt_rigid, cnt_min);
  return 0;
}
