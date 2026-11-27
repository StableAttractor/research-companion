# Sp(4,2)-orbits (= graph isomorphism classes) of the minimal forbidden rank-4 multisets, and of tripled bases.
import itertools, sys
def om(x,y):
    a=((x&1)&((y>>1)&1))^(((x>>1)&1)&(y&1)); b=(((x>>2)&1)&((y>>3)&1))^(((x>>3)&1)&((y>>2)&1)); return a^b
vecs=list(range(1,16))
# enumerate linear maps by images of e1..e4, keep those preserving om and invertible
G=[]
for imgs in itertools.product(range(1,16),repeat=4):
    def ap(x): 
        r=0
        for i in range(4):
            if x>>i&1: r^=imgs[i]
        return r
    if any(om(1<<i,1<<j)!=om(imgs[i],imgs[j]) for i in range(4) for j in range(4)): continue
    perm=[0]+[ap(x) for x in vecs]
    if len(set(perm[1:]))==15: G.append(perm)
print("|Sp(4,2)| =",len(G))
def canon(ms):
    return min(tuple(sorted(g[x] for x in ms)) for g in G)
import networkx as nx
for n in range(7,12):
    reps=set(canon(tuple(map(int,l.split()))) for l in open(f"min_n{n}.txt"))
    print(f"n={n}: minimal forbidden multisets -> {len(reps)} isomorphism classes")
# tripled bases
bases=[B for B in itertools.combinations(vecs,4)]
def rk(vs):
    b=[]
    for v in vs:
        for x in b: v=min(v,v^x)
        if v: b.append(v)
    return len(b)
bases=[B for B in bases if rk(B)==4]
reps=set(canon(tuple(sorted(B*3))) for B in bases)
print("unordered bases:",len(bases),"; orbits of their triplings:",len(reps))
# cross-check: orbit representatives pairwise non-isomorphic as graphs (n=8,9,11)
def graph(ms):
    g=nx.Graph(); g.add_nodes_from(range(len(ms)))
    for i in range(len(ms)):
        for j in range(i+1,len(ms)):
            if om(ms[i],ms[j]): g.add_edge(i,j)
    return g
for n in (8,9,11):
    reps=sorted(set(canon(tuple(map(int,l.split()))) for l in open(f"min_n{n}.txt")))
    gs=[graph(r) for r in reps]
    clash=sum(1 for i in range(len(gs)) for j in range(i+1,len(gs)) if nx.is_isomorphic(gs[i],gs[j]))
    print(f"n={n}: {len(gs)} orbit reps, isomorphic pairs among them: {clash}")
