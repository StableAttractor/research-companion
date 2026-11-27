# Graph-by-graph comparison of the enumerated minimal forbidden graphs for mr(F_2, G) <= k (log E)
# with the published lists:
#   k = 1: P3, 2K2
#   k = 2: Barrett, van der Holst, Loewy (2005), Theorem 16: P4, dart, (diamond u K1)^c, P3 u K2, 3K2,
#          (2K2 u 2K1)^c = P3 v P3, (P3 u 2K1)^c
#   k = 3: Barrett, Grout, Loewy (2009), Theorem 49: 62 graphs given by graph6 codes (data/BGL_2009_Theorem49_graph6.txt)
# It also re-computes, with code independent of the C enumeration, that every published graph G has
# mr(F_2, G) = k + 1 and mr(F_2, G - v) <= k for every vertex v.
# Requires networkx (isomorphism testing only).
import re, itertools, os, sys
import networkx as nx
here = os.path.dirname(os.path.abspath(__file__)); root = os.path.dirname(here)

def from_graph6(s):
    b = [ord(ch) - 63 for ch in s]; n = b[0]; bits = []
    for v in b[1:]:
        bits += [(v >> k) & 1 for k in range(5, -1, -1)]
    G = nx.Graph(); G.add_nodes_from(range(n)); t = 0
    for j in range(1, n):
        for i in range(j):
            if bits[t]: G.add_edge(i, j)
            t += 1
    return G

def mr_f2(G):
    """Least rank over F_2 of A(G) + D, D diagonal: brute force over all 2^n diagonals."""
    V = sorted(G.nodes()); n = len(V); idx = {v: i for i, v in enumerate(V)}
    rows0 = [0] * n
    for u, v in G.edges():
        rows0[idx[u]] |= 1 << idx[v]; rows0[idx[v]] |= 1 << idx[u]
    best = n
    for d in range(1 << n):
        rows = [rows0[i] | (((d >> i) & 1) << i) for i in range(n)]
        r = 0
        for i in range(n):
            if not rows[i]: continue
            low = rows[i] & -rows[i]; r += 1
            for t in range(i + 1, n):
                if rows[t] & low: rows[t] ^= rows[i]
        best = min(best, r)
    return best

def is_minimal_forbidden(G, k):
    if mr_f2(G) != k + 1: return False
    return all(mr_f2(G.subgraph([u for u in G if u != v])) <= k for v in G)

def parse_enumeration(path):
    """Returns {k: [graphs]} from the output of forbidden_graphs_f2.c."""
    out = {}; k = None
    for line in open(path):
        m = re.match(r"\s*k=(\d+) ", line)
        if m: k = int(m.group(1)); out.setdefault(k, []); continue
        m = re.match(r"\s*n=(\d+)(?: c k=(\d+))?: .*isomorphism:(.*)", line)
        if m:
            n = int(m.group(1)); kk = int(m.group(2)) if m.group(2) else k
            for e in re.findall(r"\{([0-9,]*)\}", m.group(3)):
                G = nx.Graph(); G.add_nodes_from(range(n))
                for pair in e.split(","):
                    G.add_edge(int(pair[0]), int(pair[1]))
                out.setdefault(kk, []).append(G)
    return out

def match(ours, published, names):
    used = set(); res = []
    for i, P in enumerate(published):
        hit = None
        for j, O in enumerate(ours):
            if j in used: continue
            if O.number_of_nodes() == P.number_of_nodes() and O.number_of_edges() == P.number_of_edges() and nx.is_isomorphic(O, P):
                hit = j; break
        if hit is not None: used.add(hit)
        res.append((names[i], hit))
    return res, [j for j in range(len(ours)) if j not in used]

def comp(G): return nx.complement(G)
def du(*gs): return nx.disjoint_union_all(gs)
K = lambda n: nx.complete_graph(n); P = lambda n: nx.path_graph(n)
paw = comp(du(K(1), P(3))); diamond = comp(du(K(1), K(1), K(2)))
pub = {
 1: ([P(3), du(K(2), K(2))], ["P3", "2K2"]),
 2: ([P(4), comp(du(K(1), paw)), comp(du(diamond, K(1))), du(P(3), K(2)), du(K(2), K(2), K(2)),
      comp(du(K(2), K(2), K(1), K(1))), comp(du(P(3), K(1), K(1)))],
     ["P4", "dart = (K1 u paw)^c", "(diamond u K1)^c", "P3 u K2", "3K2", "(2K2 u 2K1)^c = P3 v P3", "(P3 u 2K1)^c"]),
}
codes = [l.split() for l in open(os.path.join(root, "data", "BGL_2009_Theorem49_graph6.txt")) if l.strip() and not l.startswith("#")]
pub[3] = ([from_graph6(c) for _, c in codes], ["BGL graph %s (%s)" % (n, c) for n, c in codes])

ours = parse_enumeration(os.path.join(root, "logs", "E_forbidden_graphs_f2.txt"))
allok = True
for k in (1, 2, 3):
    P_, names = pub[k]; O = ours.get(k, [])
    res, extra = match(O, P_, names)
    missing = [nm for nm, h in res if h is None]
    indep = [is_minimal_forbidden(G, k) for G in P_]
    sizes = {}
    for G in P_: sizes[G.number_of_nodes()] = sizes.get(G.number_of_nodes(), 0) + 1
    print("k = %d: published %d graphs (by number of vertices: %s); enumerated %d graphs" % (k, len(P_), dict(sorted(sizes.items())), len(O)))
    print("   published graphs matched one-to-one by an enumerated graph (isomorphism): %d of %d" % (len(P_) - len(missing), len(P_)))
    print("   published graphs with no match: %s" % (missing or "none"))
    print("   enumerated graphs not in the published list: %d" % len(extra))
    print("   independent check, each published graph has mr = %d and every vertex-deleted subgraph has mr <= %d: %d of %d" % (k + 1, k, sum(indep), len(P_)))
    print("   largest published graph: %d vertices; 2k + 2 = %d" % (max(sizes), 2 * k + 2))
    ok = (not missing) and (not extra) and all(indep) and len(O) == len(P_)
    allok &= ok
    print("   RESULT: %s" % ("lists identical" if ok else "DISCREPANCY"))
print("OVERALL: %s" % ("all three lists agree graph by graph" if allok else "DISCREPANCY FOUND"))
