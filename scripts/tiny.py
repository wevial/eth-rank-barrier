# Exact check of the (r,Q,R) = (2,3,2) case: swap-span optimum vs block-adapted matrix.
# B = ([r]x[r])^Q, u = (a,d). Swap s exchanges a(s), d(s). Support condition P_R:
# M[u,w] != 0 only if #{s : a_w(s) != d_u(s)} <= R-1.  Defect = rank_Q(I - M).
from fractions import Fraction as F
from itertools import product, combinations
r, Q, R = 2, 3, 2
words = list(product(range(r), repeat=Q))
B = [(a, d) for a in words for d in words]
idx = {u: i for i, u in enumerate(B)}
N = len(B)

def swap(u, S):                     # swap coordinates in S
    a, d = list(u[0]), list(u[1])
    for s in S: a[s], d[s] = d[s], a[s]
    return (tuple(a), tuple(d))

def perm(S):                        # matrix of the product of swaps in S
    M = [[F(0)] * N for _ in range(N)]
    for u in B: M[idx[u]][idx[swap(u, S)]] = F(1)
    return M

def add(A, Bm, c=F(1)): return [[x + c * y for x, y in zip(ra, rb)] for ra, rb in zip(A, Bm)]
def zero(): return [[F(0)] * N for _ in range(N)]

def rank(M):
    M = [row[:] for row in M]; rk = 0
    for c in range(N):
        p = next((i for i in range(rk, N) if M[i][c] != 0), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        for i in range(rk + 1, N):
            if M[i][c] != 0:
                f = M[i][c] / M[rk][c]
                M[i] = [x - f * y for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk

def defect(M): return rank([[(F(1) if i == j else F(0)) - M[i][j] for j in range(N)] for i in range(N)])
def in_support(M):
    return all(M[idx[u]][idx[w]] == 0 or sum(w[0][s] != u[1][s] for s in range(Q)) <= R - 1
               for u in B for w in B)

full = tuple(range(Q))
def leave(S): return perm(tuple(s for s in full if s not in S))   # Pi_{[Q]\S}

# --- swap span: M = g0*Pi_all + sum_s g_s*Pi_{[Q]\{s}}; eigenvalue on signs x is parity(x)*g(x)
signs = list(product((1, -1), repeat=Q))
mult = {x: 1 for x in signs}
for x in signs:
    m = 1
    for xs in x: m *= (r * (r + 1) // 2) if xs == 1 else (r * (r - 1) // 2)
    mult[x] = m
par = lambda x: 1 if sum(v == -1 for v in x) % 2 == 0 else -1

def solve_affine(A):                # exact g = (g0,g1..gQ) with g(x)=par(x) on A, or None
    rows = [[F(1)] + [F(v) for v in x] + [F(par(x))] for x in A]
    piv = []; rk = 0
    for c in range(Q + 1):
        p = next((i for i in range(rk, len(rows)) if rows[i][c] != 0), None)
        if p is None: continue
        rows[rk], rows[p] = rows[p], rows[rk]
        rows[rk] = [v / rows[rk][c] for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] != 0:
                f = rows[i][c]; rows[i] = [v - f * w for v, w in zip(rows[i], rows[rk])]
        piv.append(c); rk += 1
    if any(all(v == 0 for v in row[:-1]) and row[-1] != 0 for row in rows): return None
    g = [F(0)] * (Q + 1)
    for i, c in enumerate(piv): g[c] = rows[i][-1]
    return g

best = None
for k in range(len(signs), 0, -1):
    for A in combinations(signs, k):
        g = solve_affine(A)
        if g is None: continue
        err = sum(mult[x] for x in signs if g[0] + sum(gi * xi for gi, xi in zip(g[1:], x)) != par(x))
        if best is None or err < best[0]: best = (err, g)
err, g = best
M = zero(); M = add(M, leave(()), g[0])
for s in range(Q): M = add(M, leave((s,)), g[s + 1])
print("swap-span optimum: predicted defect", err, "| g =", [str(v) for v in g],
      "| exact rank(I-M) =", defect(M), "| support ok:", in_support(M))

# --- block-adapted: block = which coordinates have a(s) != d(s); interval {0,1} if k<=2, {1,2} if k=3
V0 = leave(())
Madapt = zero()
for u in B:
    k = sum(u[0][s] != u[1][s] for s in range(Q))
    c0, c1 = (F(1), F(-2)) if k <= 2 else (F(-3), F(2))     # f(j) = c0 + c1*j
    # row u of V0*f(W0) = (c0 + c1*Q/2)*V0 - (c1/2)*sum_s Pi_{[Q]\{s}}
    i = idx[u]
    Madapt[i][idx[swap(u, full)]] += c0 + c1 * F(Q, 2)
    for s in range(Q):
        Madapt[i][idx[swap(u, tuple(t for t in full if t != s))]] += -c1 / 2
print("block-adapted: exact rank(I-M) =", defect(Madapt), "| support ok:", in_support(Madapt), "| dim", N)

# --- controls: identity is outside the support; full swap alone
I = [[F(1) if i == j else F(0) for j in range(N)] for i in range(N)]
print("control identity: support ok:", in_support(I), "(must be False)")
print("control full swap only: rank(I-M) =", defect(V0), "| support ok:", in_support(V0))
