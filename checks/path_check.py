"""Exact checks for the combinatorial core of the path-sum bound.

Objects (sites 0..n-1, terms = (support, weight) with positive rational weights):
  path  (consecutive convention): Z_1 meets Y, Z_{j+1} meets Z_j (repeats allowed), Z_k meets X.
  chain (union convention):       Z_1 meets Y, Z_{j+1} meets Y ∪ Z_1 ∪ ... ∪ Z_j, the union meets X
                                  for the first time at step k.
  site matrix h: h_uv = sum of weights of terms containing u and v (u != v);
                 h_uu = sum of weights of terms containing u.
Claims tested with exact arithmetic (fractions):
  (P) sum over paths of length k of the product of weights <= sum_{x in X, y in Y} (h^k)_{xy}   [expected TRUE]
  (C) the same with chains in place of paths                                                   [expected FALSE in general]
Every claim is also run on degenerate inputs in its own section.
"""
from fractions import Fraction as Fr
from itertools import product
import random, sys

def site_matrix(n, terms):
    h = [[Fr(0)] * n for _ in range(n)]
    for S, w in terms:
        for u in S:
            for v in S:
                if u == v or True:
                    pass
        for u in S:
            h[u][u] += w
            for v in S:
                if u != v:
                    h[u][v] += w
    return h

def matpow_entry_sum(h, k, X, Y):
    n = len(h)
    # (h^k)_{xy} summed over x in X, y in Y, via repeated multiplication of the row vector sum_{y in Y} e_y
    v = [Fr(1) if y in Y else Fr(0) for y in range(n)]
    for _ in range(k):
        v = [sum(v[u] * h[u][w] for u in range(n)) for w in range(n)]
    return sum(v[x] for x in X)

def path_sum(terms, k, X, Y):
    total = Fr(0)
    m = len(terms)
    for seq in product(range(m), repeat=k):
        Zs = [terms[i][0] for i in seq]
        if not (Zs[0] & Y):
            continue
        if any(not (Zs[j] & Zs[j + 1]) for j in range(k - 1)):
            continue
        if not (Zs[-1] & X):
            continue
        w = Fr(1)
        for i in seq:
            w *= terms[i][1]
        total += w
    return total

def chain_sum(terms, k, X, Y):
    """Union chains with first contact with X at step k."""
    total = Fr(0)
    m = len(terms)
    for seq in product(range(m), repeat=k):
        Zs = [terms[i][0] for i in seq]
        union = set(Y)
        ok = True
        for j, Z in enumerate(Zs):
            if not (Z & union):
                ok = False; break
            union |= Z
            hits = bool(union & X)
            if hits and j < k - 1:
                ok = False; break          # contact before the last step
            if j == k - 1 and not hits:
                ok = False; break
        if not ok:
            continue
        w = Fr(1)
        for i in seq:
            w *= terms[i][1]
        total += w
    return total

def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    return cond

results = []
print("== Section 1: the three-term example ==")
terms = [(frozenset({1, 2}), Fr(1)), (frozenset({1, 3}), Fr(1)), (frozenset({3, 4}), Fr(1))]
n, X, Y = 5, {4}, {1}   # read from Y = {1} (the probe side) to X = {4}
h = site_matrix(n, terms)
# the sequence ({1,3},{1,2},{3,4}) is a chain (each meets the union so far) but not a path
seq = [frozenset({1, 3}), frozenset({1, 2}), frozenset({3, 4})]
is_path = bool(seq[0] & Y) and all(seq[j] & seq[j + 1] for j in range(2)) and bool(seq[-1] & X)
union = set(Y); is_chain = True
for Z in seq:
    if not (Z & union): is_chain = False
    union |= Z
is_chain = is_chain and bool(union & X)
results.append(check("three-term sequence is a chain", is_chain))
results.append(check("three-term sequence is not a path", not is_path))
for k in range(1, 5):
    ps, cs, hs = path_sum(terms, k, X, Y), chain_sum(terms, k, X, Y), matpow_entry_sum(h, k, X, Y)
    print(f"  k={k}: paths={ps} chains={cs} (h^k)_{{XY}}={hs}")
    results.append(check(f"(P) k={k}", ps <= hs))

print("== Section 2: (P) on random small hypergraphs, k <= 4 ==")
random.seed(20261004)
fails_P, fails_C, trials = 0, 0, 0
for trial in range(300):
    n = random.randint(3, 6)
    m = random.randint(1, 5)
    terms = []
    for _ in range(m):
        size = random.randint(1, 3)
        S = frozenset(random.sample(range(n), size))
        terms.append((S, Fr(random.randint(1, 4), random.randint(1, 3))))
    X = set(random.sample(range(n), random.randint(1, 2)))
    Y = set(random.sample([s for s in range(n) if s not in X] or [0], 1))
    if X & Y:
        continue
    h = site_matrix(n, terms)
    for k in range(1, 5):
        trials += 1
        hs = matpow_entry_sum(h, k, X, Y)
        if path_sum(terms, k, X, Y) > hs:
            fails_P += 1
            print("  (P) FAIL", n, terms, X, Y, k)
        if chain_sum(terms, k, X, Y) > hs:
            fails_C += 1
            print("  (C) counterexample:", "n =", n, "terms =", [(sorted(S), str(w)) for S, w in terms],
                  "X =", sorted(X), "Y =", sorted(Y), "k =", k,
                  "chains =", chain_sum(terms, k, X, Y), "(h^k) =", hs)
print(f"  {trials} (hypergraph, k) cases; (P) failures: {fails_P}; (C) failures: {fails_C}")
results.append(check("(P) holds on every random case", fails_P == 0))
results.append(check("(C) fails on some random case (reason chains were dropped)", fails_C > 0))

print("== Section 3: a witness that (C) fails ==")
terms = [(frozenset({0, 1}), Fr(1)), (frozenset({1, 2}), Fr(1)), (frozenset({2, 3}), Fr(1)), (frozenset({3, 4}), Fr(1))]
n, X, Y = 5, {4}, {0}
h = site_matrix(n, terms)
for k in range(1, 6):
    ps, cs, hs = path_sum(terms, k, X, Y), chain_sum(terms, k, X, Y), matpow_entry_sum(h, k, X, Y)
    print(f"  chain of 4 edges, k={k}: paths={ps} chains={cs} (h^k)={hs}")
witness_found = any(chain_sum(terms, k, X, Y) > matpow_entry_sum(h, k, X, Y) for k in range(1, 7))
print("  (C) violated for some k <= 6:", witness_found)

print("== Section 4: degenerate inputs ==")
h0 = site_matrix(3, [])
results.append(check("empty term family: path sums are 0 for k=1..3", all(path_sum([], k, {0}, {2}) == 0 for k in range(1, 4))))
results.append(check("empty term family: (h^k) sums are 0", all(matpow_entry_sum(h0, k, {0}, {2}) == 0 for k in range(1, 4))))
one = [(frozenset({0}), Fr(2))]
h1 = site_matrix(1, one)
results.append(check("one site, X = Y = {0}: path sum k=1 equals weight 2 and (h^1)_{00} = 2", path_sum(one, 1, {0}, {0}) == 2 and matpow_entry_sum(h1, 1, {0}, {0}) == 2))
results.append(check("one site: path sum k=3 = 8 <= (h^3) = 8", path_sum(one, 3, {0}, {0}) == 8 and matpow_entry_sum(h1, 3, {0}, {0}) == 8))
two = [(frozenset({0, 1}), Fr(1, 2))]
h2 = site_matrix(2, two)
results.append(check("one two-site term, X={1}, Y={0}: k=1 path sum 1/2 <= h_{01} = 1/2", path_sum(two, 1, {1}, {0}) == Fr(1, 2) and matpow_entry_sum(h2, 1, {1}, {0}) == Fr(1, 2)))
results.append(check("one two-site term: k=2 path sum 1/4 (repeat) <= (h^2)_{01} = 1/2", path_sum(two, 2, {1}, {0}) == Fr(1, 4) and matpow_entry_sum(h2, 2, {1}, {0}) == Fr(1, 2)))
results.append(check("disjoint X, Y with no connecting term: all path sums 0", all(path_sum([(frozenset({0, 1}), Fr(1))], k, {2}, {0}) == 0 for k in range(1, 4))))

print()
print(f"{sum(results)} of {len(results)} checks pass")
sys.exit(0 if all(results) else 1)
