# Lower bounds for min rank(I - M) over ALL M with the support pattern P_R.
# N = I - M has N[u,u] = 1 forced when (u,u) is outside P_R, and N[u,w] = 0 forced when (u,w) is outside P_R.
# Any set S of forced-diagonal vertices whose allowed-entry digraph is acyclic gives a unit-triangular
# minor, so rank >= |S|.  (1) check Opus's explicit set; (2) find the largest such set exactly.
import sys
from itertools import product
r, Q, R = (int(x) for x in sys.argv[1:4])
words = list(product(range(r), repeat=Q))
B = [(a, d) for a in words for d in words]
N = len(B)
mism = lambda u, w: sum(w[0][s] != u[1][s] for s in range(Q))      # #{s : a_w(s) != d_u(s)}
allowed = lambda u, w: mism(u, w) <= R - 1
forced = [i for i, u in enumerate(B) if not allowed(u, u)]
out = {i: 0 for i in forced}                                         # bitmask over positions in `forced`
pos = {v: k for k, v in enumerate(forced)}
for i in forced:
    for j in forced:
        if i != j and allowed(B[i], B[j]): out[i] |= 1 << pos[j]
outm = [out[v] for v in forced]
F = len(forced)

def acyclic(mask):                    # Kahn on bitmasks: repeatedly strip vertices with no out-edge inside
    while mask:
        m, strip = mask, 0
        while m:
            b = m & -m; k = b.bit_length() - 1
            if outm[k] & mask == 0: strip |= b
            m ^= b
        if not strip: return False
        mask ^= strip
    return True

# (1) Opus's set: kappa(d) - kappa(a) >= R with kappa = number of letters above floor(r/2) (letters 1..r)
h = lambda x: 1 if (x + 1) > r // 2 else 0
kap = lambda y: sum(h(x) for x in y)
Sset = [i for i, u in enumerate(B) if kap(u[1]) - kap(u[0]) >= R]
ok_forced = all(i in pos for i in Sset)
smask = sum(1 << pos[i] for i in Sset) if ok_forced else 0
print(f"(r,Q,R)=({r},{Q},{R}) dim {N}: forced-diagonal vertices {F}")
print(f"  Opus's set: size {len(Sset)}, all forced-diagonal: {ok_forced}, acyclic: {ok_forced and acyclic(smask)}")

# (2) exact maximum acyclic induced set among forced vertices (acyclicity is hereditary, so DFS by extension)
best = [0, 0]
def dfs(mask, size, start):
    if size > best[0]: best[0], best[1] = size, mask
    if size + (F - start) <= best[0]: return
    for k in range(start, F):
        if size + (F - k) <= best[0]: return
        nm = mask | (1 << k)
        if acyclic(nm): dfs(nm, size + 1, k + 1)
sys.setrecursionlimit(10000)
dfs(0, 0, 0)
print(f"  largest acyclic forced set (exact): {best[0]}")
print("  one such set (a,d):", [B[forced[k]] for k in range(F) if best[1] >> k & 1])
