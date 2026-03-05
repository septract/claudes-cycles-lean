#!/usr/bin/env python3
"""Enumerate Claude-like decompositions and verify Knuth's counts.

Expected results (from Knuth's paper, p.4):
- 11502 Hamiltonian cycles at m=3
- 1012 of those generalize to m=5
- 996 generalize to both m=5 and m=7
- 4554 decompositions (unordered triples of cycles covering all arcs)
- 760 decompositions using only generalizable cycles

Reference: Don Knuth, "Claude's Cycles" (Feb 2026).
"""

import time
import sys
from collections import defaultdict

# ---------- Vertex encoding/decoding ----------

def encode(m, i, j, k):
    return m * m * i + m * j + k

def decode(m, v):
    i = v // (m * m)
    r = v % (m * m)
    j = r // m
    k = r % m
    return i, j, k

def bump(m, v, d):
    i, j, k = decode(m, v)
    if d == 0:
        return encode(m, (i + 1) % m, j, k)
    elif d == 1:
        return encode(m, i, (j + 1) % m, k)
    else:
        return encode(m, i, j, (k + 1) % m)

# Precompute bump tables for small m
_bump_cache = {}

def get_bump_table(m):
    if m not in _bump_cache:
        total = m ** 3
        table = [[0] * 3 for _ in range(total)]
        for v in range(total):
            for d in range(3):
                table[v][d] = bump(m, v, d)
        _bump_cache[m] = table
    return _bump_cache[m]

# ---------- Coarsen and lift ----------

def coarsen(m, x):
    """0 -> 0, m-1 -> 2, else -> 1."""
    if x == 0:
        return 0
    elif x == m - 1:
        return 2
    else:
        return 1

def make_coarsened_table(dir3):
    """Extract the 27-entry coarsened table from an m=3 direction function.

    At m=3, coarsen is the identity, so (s_bar, i_bar, j_bar) = (s, i, j).
    The vertex with fiber s and coordinates (i, j) has k = (s - i - j) % 3.
    """
    ct = [[[0] * 3 for _ in range(3)] for _ in range(3)]
    for s in range(3):
        for i in range(3):
            for j in range(3):
                k = (s - i - j) % 3
                v = encode(3, i, j, k)
                ct[s][i][j] = dir3[v]
    return ct

def make_lift_table(dir3, m):
    """Given a direction function at m=3, build direction table for m.

    dir3: tuple of 27 values (direction at each m=3 vertex).
    The coarsened table is extracted from dir3, then applied at m.
    """
    ct = make_coarsened_table(dir3)
    total = m ** 3
    table = [0] * total
    for v in range(total):
        i, j, k = decode(m, v)
        s = (i + j + k) % m
        table[v] = ct[coarsen(m, s)][coarsen(m, i)][coarsen(m, j)]
    return table

# ---------- Hamiltonicity check ----------

def orbit_length(m, dir_table, start):
    """Compute orbit length from start using precomputed tables."""
    bt = get_bump_table(m)
    total = m ** 3
    v = bt[start][dir_table[start]]
    n = 1
    while v != start:
        v = bt[v][dir_table[v]]
        n += 1
        if n > total:
            return n  # safety
    return n

def is_hamiltonian(m, dir_table):
    return orbit_length(m, dir_table, 0) == m ** 3

# ---------- Enumerate Hamiltonian cycles at m=3 ----------

def enumerate_cycles_m3():
    """Find all Hamiltonian cycles in the m=3 digraph by backtracking."""
    m = 3
    total = 27
    bt = get_bump_table(m)
    cycles = []
    dirs = [0] * total
    visited = bytearray(total)  # 0 or 1

    def backtrack(cur, depth):
        if depth == total:
            # Must return to vertex 0
            for d in range(3):
                if bt[cur][d] == 0:
                    dirs[cur] = d
                    cycles.append(tuple(dirs))
            return

        for d in range(3):
            nxt = bt[cur][d]
            if not visited[nxt]:
                dirs[cur] = d
                visited[nxt] = 1
                backtrack(nxt, depth + 1)
                visited[nxt] = 0

    visited[0] = 1
    backtrack(0, 1)
    return cycles

# ---------- Find decompositions ----------

def find_decompositions(cycles):
    """Find all unordered triples of cycles that partition all arcs.

    Three cycles form a decomposition iff at every vertex, their directions
    are a permutation of {0,1,2}. Equivalently: pairwise different at each vertex.
    """
    n = len(cycles)
    cycle_set = set(cycles)
    cycle_idx = {c: i for i, c in enumerate(cycles)}
    decomps = []

    # For each pair (i,j) with i < j, check compatibility and complement
    # Optimization: group cycles by direction at vertex 0
    by_dir0 = defaultdict(list)
    for i, c in enumerate(cycles):
        by_dir0[c[0]].append(i)

    # In a decomposition, the three cycles use directions {0,1,2} at vertex 0.
    # So one cycle from each group.
    groups = [by_dir0[0], by_dir0[1], by_dir0[2]]
    print(f"  Cycles by dir[0]: {len(groups[0])}, {len(groups[1])}, {len(groups[2])}")

    for i_idx in groups[0]:
        c0 = cycles[i_idx]
        for j_idx in groups[1]:
            c1 = cycles[j_idx]
            # Check compatibility: differ at every vertex
            compatible = True
            c2_list = [0] * 27
            for v in range(27):
                if c0[v] == c1[v]:
                    compatible = False
                    break
                c2_list[v] = 3 - c0[v] - c1[v]
            if not compatible:
                continue
            c2 = tuple(c2_list)
            if c2 in cycle_set:
                k_idx = cycle_idx[c2]
                # Store as sorted triple of indices
                triple = tuple(sorted([i_idx, j_idx, k_idx]))
                decomps.append(triple)

    # Deduplicate (each unordered triple appears once since we fixed dir[0])
    decomps = list(set(decomps))
    return decomps

# ---------- Main ----------

def main():
    print("=" * 60)
    print("Verifying Knuth's counts for Claude-like decompositions")
    print("=" * 60)

    # Step 1: Enumerate Hamiltonian cycles at m=3
    t0 = time.time()
    print("\n[1] Enumerating Hamiltonian cycles at m=3...")
    cycles = enumerate_cycles_m3()
    print(f"    Found: {len(cycles)}  (expected: 11502)")
    print(f"    Time: {time.time() - t0:.1f}s")

    # Step 2: Check generalizability at m=5
    t1 = time.time()
    print("\n[2] Checking which cycles generalize to m=5...")
    gen5 = []
    for c in cycles:
        dt = make_lift_table(c, 5)
        if is_hamiltonian(5, dt):
            gen5.append(c)
    print(f"    Generalize to m=5: {len(gen5)}  (expected: 1012)")
    print(f"    Time: {time.time() - t1:.1f}s")

    # Step 3: Check generalizability at m=7
    t2 = time.time()
    print("\n[3] Checking which also generalize to m=7...")
    gen7 = []
    for c in gen5:
        dt = make_lift_table(c, 7)
        if is_hamiltonian(7, dt):
            gen7.append(c)
    print(f"    Generalize to m=5 AND m=7: {len(gen7)}  (expected: 996)")
    print(f"    Time: {time.time() - t2:.1f}s")

    # Step 3b: Bonus checks for the 996 cycles at m=9,11,13
    for test_m in [9, 11, 13]:
        t2b = time.time()
        count = sum(1 for c in gen7 if is_hamiltonian(test_m, make_lift_table(c, test_m)))
        print(f"[3b] Also generalize to m={test_m}: {count}  [{time.time() - t2b:.1f}s]")

    # Step 3c: Analyze the 16 cycles that work at m=5 but fail at m=7
    fail7 = [c for c in gen5 if c not in set(gen7)]
    print(f"\n[3c] Cycles that generalize to m=5 but NOT m=7: {len(fail7)}")
    if fail7:
        # Check orbit lengths at m=7 to see how they fail
        for idx, c in enumerate(fail7[:5]):
            dt = make_lift_table(c, 7)
            olen = orbit_length(7, dt, 0)
            print(f"     Cycle {idx}: orbit at m=7 has length {olen} (need 343)")

    # Step 4: Find all decompositions at m=3
    t3 = time.time()
    print("\n[4] Finding all decompositions at m=3...")
    decomps = find_decompositions(cycles)
    print(f"    Unordered decompositions: {len(decomps)}  (expected: 4554 or 759)")
    print(f"    × 6 (labeled): {6 * len(decomps)}")
    print(f"    Time: {time.time() - t3:.1f}s")

    # Step 5: Count decompositions using only generalizable cycles
    t4 = time.time()
    print("\n[5] Counting generalizable decompositions...")
    cycle_set = set(cycles)
    gen7_set = set(gen7)
    gen_decomps = [
        d for d in decomps
        if cycles[d[0]] in gen7_set
        and cycles[d[1]] in gen7_set
        and cycles[d[2]] in gen7_set
    ]
    print(f"    Generalizable decompositions: {len(gen_decomps)}  (expected: 760 or ~127)")
    print(f"    × 6 (labeled): {6 * len(gen_decomps)}")
    print(f"    Time: {time.time() - t4:.1f}s")

    print(f"\n{'=' * 60}")
    print(f"Total time: {time.time() - t0:.1f}s")
    print(f"{'=' * 60}")

    # Step 6: Identify Claude's specific decomposition
    print("\n[6] Identifying Claude's specific decomposition...")
    # Claude's direction function for cycle c at vertex (i,j,k) mod 3
    def claude_dir(c, i, j, k, m=3):
        s = (i + j + k) % m
        if c == 0:
            if s == 0:
                return 0 if j == m - 1 else 2
            elif s == m - 1:
                return 1 if i != 0 else 2
            else:
                return 2 if i == m - 1 else 1
        elif c == 1:
            if s == 0:
                return 1
            elif s == m - 1:
                return 2 if i != 0 else 1
            else:
                return 0
        else:  # c == 2
            if s == 0:
                return 0 if j != m - 1 else 2
            elif s == m - 1:
                return 0
            else:
                return 2 if i != m - 1 else 1

    claude_cycles = []
    for c in range(3):
        d = tuple(claude_dir(c, *decode(3, v)) for v in range(27))
        claude_cycles.append(d)
        idx = cycles.index(d) if d in cycle_set else -1
        is_gen = d in gen7_set
        print(f"    Cycle {c}: index {idx}, generalizable: {is_gen}")

    # Check if Claude's decomposition is among the 760
    claude_triple = tuple(sorted([
        cycles.index(claude_cycles[0]),
        cycles.index(claude_cycles[1]),
        cycles.index(claude_cycles[2])
    ]))
    is_760 = claude_triple in set(gen_decomps)
    print(f"    Claude's decomposition among 760: {is_760}")

    # Step 7: Classification of the 996 generalizable cycles
    print("\n[7] Classifying the 996 generalizable cycles by interior behavior...")
    # Interior = entries with s_bar = 1 (6 entries: i_bar × j_bar = 3 × 3, minus s_bar=0,2)
    # Actually s_bar=1 gives 9 entries (i_bar in {0,1,2}, j_bar in {0,1,2})
    interior_patterns = defaultdict(list)
    for c in gen7:
        ct = make_coarsened_table(c)
        interior = tuple(ct[1][i][j] for i in range(3) for j in range(3))
        interior_patterns[interior].append(c)
    print(f"    Distinct interior patterns: {len(interior_patterns)}")
    for pat, cycs in sorted(interior_patterns.items(), key=lambda x: -len(x[1])):
        print(f"      {pat}: {len(cycs)} cycles")

    # Step 8: Export the 760 tables for potential Lean embedding
    if "--export" in sys.argv:
        export_path = "compute/tables_760.json"
        import json
        tables_data = []
        for d in gen_decomps:
            c0, c1, c2 = cycles[d[0]], cycles[d[1]], cycles[d[2]]
            ct0 = make_coarsened_table(c0)
            ct1 = make_coarsened_table(c1)
            ct2 = make_coarsened_table(c2)
            # Table: T(c, s_bar, i_bar, j_bar)
            table = [[[ct0[s][i][j], ct1[s][i][j], ct2[s][i][j]]
                      for i in range(3) for j in range(3)]
                     for s in range(3)]
            tables_data.append(table)
        with open(export_path, "w") as f:
            json.dump(tables_data, f)
        print(f"\n[8] Exported {len(tables_data)} tables to {export_path}")

    # Summary
    print(f"\n{'=' * 60}")
    print("Summary:")
    print(f"  Hamiltonian cycles at m=3:         {len(cycles)}")
    print(f"  Generalize to m=5:                 {len(gen5)}")
    print(f"  Generalize to m=5 AND m=7:         {len(gen7)}")
    print(f"  Generalize to m=5, not m=7:        {len(fail7)}")
    print(f"  Decompositions at m=3:             {len(decomps)}")
    print(f"  Generalizable decompositions:      {len(gen_decomps)}")

if __name__ == "__main__":
    main()
