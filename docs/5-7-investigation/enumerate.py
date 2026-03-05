#!/usr/bin/env python3
"""
Enumerate all Hamiltonian cycles in the m=3 digraph on (Z/3Z)^3.
Test generalizability at m=5, m=7, m=9.
Analyze the structure of generalizable vs non-generalizable cycles.

Expected results (from Knuth's paper):
  - 11502 Hamiltonian cycles at m=3
  - 1012 generalize to m=5
  - 996 generalize to both m=5 and m=7
  - Those 996 generalize to all odd m (verified computationally up to m=101)
"""
import sys
import json
from collections import Counter, defaultdict

# ── Vertex encoding ──────────────────────────────────────────────

def encode(i, j, k, m):
    return m * m * i + m * j + k

def decode(v, m):
    k = v % m
    v //= m
    j = v % m
    i = v // m
    return (i, j, k)

def coarsen(x, m):
    """0 -> 0, m-1 -> 2, everything else -> 1."""
    if x == 0: return 0
    if x == m - 1: return 2
    return 1

def make_bump_table(m):
    """Precompute bump[v][d] for all vertices v and directions d in {0,1,2}."""
    n = m ** 3
    table = [[0] * 3 for _ in range(n)]
    for i in range(m):
        for j in range(m):
            for k in range(m):
                v = encode(i, j, k, m)
                table[v][0] = encode((i + 1) % m, j, k, m)
                table[v][1] = encode(i, (j + 1) % m, k, m)
                table[v][2] = encode(i, j, (k + 1) % m, m)
    return table

# ── Enumeration at m=3 ──────────────────────────────────────────

def enumerate_ham_cycles():
    """
    Enumerate all Hamiltonian cycles in the m=3 digraph via DFS from (0,0,0).
    Returns a list of direction tables, each a tuple of 27 directions.
    """
    m = 3
    n = 27
    bump = make_bump_table(m)
    start = 0
    direction = [0] * n
    visited = [False] * n
    visited[start] = True
    cycles = []

    def dfs(v, depth):
        for d in range(3):
            next_v = bump[v][d]
            if depth == n - 1:
                if next_v == start:
                    direction[v] = d
                    cycles.append(tuple(direction))
                continue
            if visited[next_v]:
                continue
            direction[v] = d
            visited[next_v] = True
            dfs(next_v, depth + 1)
            visited[next_v] = False

    dfs(start, 0)
    return cycles

# ── Generalizability testing ─────────────────────────────────────

def lifted_direction(dir_table, v, m):
    """Compute the direction for vertex v (encoded) at general m, using m=3 table."""
    i, j, k = decode(v, m)
    s = (i + j + k) % m
    s_bar = coarsen(s, m)
    i_bar = coarsen(i, m)
    j_bar = coarsen(j, m)
    k_bar = (s_bar - i_bar - j_bar) % 3
    m3_v = encode(i_bar, j_bar, k_bar, 3)
    return dir_table[m3_v]

def orbit_length(dir_table, m, start=0):
    """
    Compute the orbit length from `start` under the lifted step function.
    Returns the period (equals m^3 iff Hamiltonian).
    """
    bump = make_bump_table(m)
    n = m ** 3
    v = start
    for step in range(1, n + 1):
        d = lifted_direction(dir_table, v, m)
        v = bump[v][d]
        if v == start:
            return step
    return n + 1  # not a permutation (shouldn't happen for valid tables)

def is_hamiltonian(dir_table, m):
    return orbit_length(dir_table, m) == m ** 3

# ── Table representation ─────────────────────────────────────────

def table_as_sij(dir_table):
    """
    Convert a direction table (indexed by encoded m=3 vertex) to a dict
    keyed by (s_bar, i_bar, j_bar).
    """
    d = {}
    for v in range(27):
        i, j, k = decode(v, 3)
        s = (i + j + k) % 3
        d[(s, i, j)] = dir_table[v]
    return d

def table_str(dir_table):
    """Pretty-print the direction table organized by s_bar."""
    t = table_as_sij(dir_table)
    lines = []
    s_labels = ["s=0", "s=mid", "s=m-1"]
    for s in range(3):
        entries = []
        for i in range(3):
            for j in range(3):
                entries.append(str(t[(s, i, j)]))
        lines.append(f"  {s_labels[s]}: [{' '.join(entries)}]  (i=0..2, j=0..2)")
    return '\n'.join(lines)

def interior_subtable(dir_table):
    """Extract the 9-entry interior subtable (s_bar=1)."""
    t = table_as_sij(dir_table)
    return tuple(t[(1, i, j)] for i in range(3) for j in range(3))

# ── M-step map analysis ─────────────────────────────────────────

def compute_m_step_map(dir_table, m):
    """
    Compute the m-step map: for each fiber-0 vertex, iterate m steps to
    get the next fiber-0 vertex. Returns a dict mapping (i,j) -> (i',j').
    """
    bump = make_bump_table(m)
    n = m ** 3
    m_step = {}
    for I in range(m):
        for J in range(m):
            K = (- I - J) % m  # fiber 0 vertex: I+J+K = 0 mod m
            v = encode(I, J, K, m)
            # Take m steps
            for _ in range(m):
                d = lifted_direction(dir_table, v, m)
                v = bump[v][d]
            I2, J2, K2 = decode(v, m)
            assert (I2 + J2 + K2) % m == 0, f"m-step didn't return to fiber 0"
            m_step[(I, J)] = (I2, J2)
    return m_step

def analyze_m_step_map(m_step, m):
    """Analyze properties of the m-step map on (Z/mZ)^2."""
    # Check if it's a single cycle
    start = (0, 0)
    v = start
    length = 0
    for _ in range(m * m):
        v = m_step[v]
        length += 1
        if v == start:
            break

    # Check if it's affine: M(i,j) = (i+a, j+b) for all (i,j)
    # If so, find (a, b)
    deltas = set()
    for (i, j), (i2, j2) in m_step.items():
        di = (i2 - i) % m
        dj = (j2 - j) % m
        deltas.add((di, dj))

    is_affine = len(deltas) == 1

    # Check if piecewise-affine by coarsened region
    region_deltas = defaultdict(set)
    for (i, j), (i2, j2) in m_step.items():
        di = (i2 - i) % m
        dj = (j2 - j) % m
        ci = coarsen(i, m)
        cj = coarsen(j, m)
        region_deltas[(ci, cj)].add((di, dj))

    is_piecewise_affine = all(len(v) == 1 for v in region_deltas.values())

    return {
        'orbit_length': length,
        'is_affine': is_affine,
        'delta': deltas.pop() if is_affine else None,
        'is_piecewise_affine': is_piecewise_affine,
        'region_deltas': {str(k): list(v) for k, v in region_deltas.items()} if not is_affine else None,
    }

# ── Interior dynamics analysis ───────────────────────────────────

def trace_interior(dir_table, I, J, m):
    """
    Trace what happens during the m-2 interior steps (s=1,...,m-2)
    for a vertex starting with coordinates (I, J) at fiber s=0 transitioning to s=1.

    Returns the sequence of (coarsened_i, coarsened_j, direction) at each interior step.
    """
    bump_tbl = make_bump_table(m)
    # First, apply the s=0 step to get from fiber 0 to fiber 1
    K = (-I - J) % m
    v = encode(I, J, K, m)
    d0 = lifted_direction(dir_table, v, m)
    v = bump_tbl[v][d0]

    # Now trace through interior fibers s=1,...,m-2
    trace = []
    for step in range(m - 2):
        i, j, k = decode(v, m)
        ci = coarsen(i, m)
        cj = coarsen(j, m)
        d = lifted_direction(dir_table, v, m)
        trace.append((ci, cj, d))
        v = bump_tbl[v][d]

    return trace

# ── Main ─────────────────────────────────────────────────────────

def main():
    print("=" * 60)
    print("HAMILTONIAN CYCLE ENUMERATION AND GENERALIZABILITY ANALYSIS")
    print("=" * 60)

    # Step 1: Enumerate
    print("\n[1] Enumerating Hamiltonian cycles at m=3...")
    cycles = enumerate_ham_cycles()
    print(f"    Found: {len(cycles)}")

    # Step 2: Test m=5
    print("\n[2] Testing generalizability at m=5...")
    pass_m5 = set()
    for idx, c in enumerate(cycles):
        if is_hamiltonian(c, 5):
            pass_m5.add(idx)
        if (idx + 1) % 2000 == 0:
            print(f"    ... tested {idx+1}/{len(cycles)}")
    print(f"    Pass m=5: {len(pass_m5)}")

    # Step 3: Test m=7
    print("\n[3] Testing generalizability at m=7...")
    pass_m7 = set()
    fail_at_m7 = []  # (index, orbit_length_at_7)
    for idx in pass_m5:
        ol = orbit_length(cycles[idx], 7)
        if ol == 343:
            pass_m7.add(idx)
        else:
            fail_at_m7.append((idx, ol))
    print(f"    Pass m=5 AND m=7: {len(pass_m7)}")
    print(f"    Pass m=5 but FAIL m=7: {len(fail_at_m7)}")

    # Step 4: Test m=9 for the m=5&7 passers
    print("\n[4] Testing at m=9...")
    pass_m9 = 0
    for idx in pass_m7:
        if is_hamiltonian(cycles[idx], 9):
            pass_m9 += 1
    print(f"    Pass m=5, m=7, m=9: {pass_m9}")

    # Step 5: Analyze the failures at m=7
    print("\n" + "=" * 60)
    print("ANALYSIS OF CYCLES PASSING m=5 BUT FAILING m=7")
    print("=" * 60)

    for rank, (idx, ol7) in enumerate(sorted(fail_at_m7)):
        c = cycles[idx]
        print(f"\n--- Cycle #{rank+1} (enumeration index {idx}) ---")
        print(f"  m=7 orbit length from (0,0,0): {ol7}")
        print(f"  Direction table:")
        print(table_str(c))

        # Check orbit structure at m=7
        bump7 = make_bump_table(7)
        visited = set()
        orbits = []
        for sv in range(343):
            if sv not in visited:
                v = sv
                orbit = []
                while v not in visited:
                    visited.add(v)
                    orbit.append(v)
                    d = lifted_direction(c, v, 7)
                    v = bump7[v][d]
                orbits.append(len(orbit))
        orbits.sort(reverse=True)
        print(f"  m=7 orbit decomposition: {orbits}")

        # Interior subtable
        print(f"  Interior subtable (s=mid): {interior_subtable(c)}")

    # Step 6: Classify generalizable cycles by interior subtable
    print("\n" + "=" * 60)
    print("CLASSIFICATION OF 996 GENERALIZABLE CYCLES")
    print("=" * 60)

    interior_classes = defaultdict(list)
    for idx in pass_m7:
        ist = interior_subtable(cycles[idx])
        interior_classes[ist].append(idx)

    print(f"\nNumber of distinct interior subtables: {len(interior_classes)}")
    print("\nInterior subtable frequencies:")
    for ist, members in sorted(interior_classes.items(), key=lambda x: -len(x[1])):
        # Decode interior table
        labels = []
        for pos in range(9):
            i_bar = pos // 3
            j_bar = pos % 3
            labels.append(f"({i_bar},{j_bar})->{ist[pos]}")
        print(f"  {', '.join(labels)}: {len(members)} cycles")

    # Step 7: M-step map analysis for representative cycles
    print("\n" + "=" * 60)
    print("M-STEP MAP ANALYSIS")
    print("=" * 60)

    # Pick one representative from each interior class
    for ist, members in sorted(interior_classes.items(), key=lambda x: -len(x[1]))[:10]:
        idx = members[0]
        c = cycles[idx]
        print(f"\n--- Representative cycle (index {idx}), interior: {ist} ---")

        for m_val in [5, 7, 9, 11]:
            m_step = compute_m_step_map(c, m_val)
            analysis = analyze_m_step_map(m_step, m_val)
            aff_str = "AFFINE" if analysis['is_affine'] else ("piecewise-affine" if analysis['is_piecewise_affine'] else "NONLINEAR")
            delta_str = f" delta={analysis['delta']}" if analysis['is_affine'] else ""
            print(f"  m={m_val}: orbit_len={analysis['orbit_length']}, {aff_str}{delta_str}")
            if not analysis['is_affine'] and analysis['is_piecewise_affine']:
                for region, deltas in sorted(analysis['region_deltas'].items()):
                    print(f"    region {region}: delta={deltas}")

    # Step 8: Analyze which directions are used in the interior
    print("\n" + "=" * 60)
    print("INTERIOR DIRECTION USAGE PATTERNS")
    print("=" * 60)

    # For each interior entry (i_bar, j_bar), what direction is used?
    # Group the 996 cycles by which coordinates change during interior traversal
    interior_dir_patterns = Counter()
    for idx in pass_m7:
        ist = interior_subtable(cycles[idx])
        # Which directions appear in interior?
        dirs_used = set(ist)
        # Does the interior ever bump i (dir=0)?
        bumps_i = 0 in ist
        bumps_j = 1 in ist
        bumps_k = 2 in ist
        pattern = (bumps_i, bumps_j, bumps_k)
        interior_dir_patterns[pattern] += 1

    print("\nInterior direction usage (bumps_i, bumps_j, bumps_k):")
    for pattern, count in sorted(interior_dir_patterns.items()):
        print(f"  {pattern}: {count} cycles")

    # Step 9: Analyze the 16 failures more deeply
    if fail_at_m7:
        print("\n" + "=" * 60)
        print("DEEP ANALYSIS OF m=7 FAILURES")
        print("=" * 60)

        for rank, (idx, _) in enumerate(sorted(fail_at_m7)):
            c = cycles[idx]
            print(f"\n--- Failure #{rank+1} (index {idx}) ---")

            # Compare interior subtable with nearest generalizable cycle
            ist = interior_subtable(c)
            t_sij = table_as_sij(c)

            # Print full table in a compact format
            print(f"  Full table (s, i, j) -> dir:")
            for s in range(3):
                row = []
                for i in range(3):
                    for j in range(3):
                        row.append(str(t_sij[(s, i, j)]))
                print(f"    s={s}: {row}")

            # Trace interior at m=7 for a few starting vertices
            print(f"  Interior trace at m=7 for (I,J)=(0,0):")
            trace = trace_interior(c, 0, 0, 7)
            for step, (ci, cj, d) in enumerate(trace):
                print(f"    step {step+1}: coarsen(i)={ci}, coarsen(j)={cj}, dir={d}")

            print(f"  Interior trace at m=7 for (I,J)=(3,3):")
            trace = trace_interior(c, 3, 3, 7)
            for step, (ci, cj, d) in enumerate(trace):
                print(f"    step {step+1}: coarsen(i)={ci}, coarsen(j)={cj}, dir={d}")

    # Step 10: Test generalizability at larger m values for the 996
    print("\n" + "=" * 60)
    print("EXTENDED GENERALIZABILITY TESTING")
    print("=" * 60)

    test_ms = [11, 13, 15, 21, 51]
    for m_val in test_ms:
        n_pass = 0
        for idx in pass_m7:
            if is_hamiltonian(cycles[idx], m_val):
                n_pass += 1
        print(f"  m={m_val}: {n_pass}/{len(pass_m7)} pass")

    print("\nDone.")

if __name__ == "__main__":
    main()
