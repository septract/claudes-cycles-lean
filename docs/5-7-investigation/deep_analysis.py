#!/usr/bin/env python3
"""
Deep analysis of the 16 cycles that pass m=5 but fail m=7.
Focuses on:
1. What happens at m=9, 11 for the 16 failures
2. Boundary conditions that distinguish generalizable from non-generalizable
3. Algebraic structure of the m-step map
4. The "boundary-to-boundary" orbit structure
"""
import sys
from collections import defaultdict
from enumerate import (
    encode, decode, coarsen, make_bump_table,
    enumerate_ham_cycles, orbit_length, is_hamiltonian,
    lifted_direction, table_as_sij, interior_subtable,
    compute_m_step_map
)

def classify_all_cycles():
    """Classify all 11502 cycles by generalizability and interior type."""
    print("Enumerating cycles...")
    cycles = enumerate_ham_cycles()
    print(f"Found {len(cycles)} cycles")

    print("Testing m=5...")
    pass5 = set()
    for i, c in enumerate(cycles):
        if is_hamiltonian(c, 5):
            pass5.add(i)
    print(f"  Pass m=5: {len(pass5)}")

    print("Testing m=7...")
    pass7 = set()
    fail7 = set()
    for i in pass5:
        if is_hamiltonian(cycles[i], 7):
            pass7.add(i)
        else:
            fail7.add(i)
    print(f"  Pass m=7: {len(pass7)}, Fail m=7: {len(fail7)}")

    return cycles, pass5, pass7, fail7


def test_failures_extended(cycles, fail7):
    """Test the 16 failures at larger m values."""
    print("\n" + "=" * 60)
    print("TESTING 16 FAILURES AT LARGER m")
    print("=" * 60)

    for m_val in [9, 11, 13, 15, 21, 101]:
        results = []
        for idx in sorted(fail7):
            ol = orbit_length(cycles[idx], m_val)
            results.append((idx, ol, m_val**3))
        n_pass = sum(1 for _, ol, target in results if ol == target)
        print(f"\n  m={m_val} (target orbit: {m_val**3}):")
        print(f"    Pass: {n_pass}/{len(fail7)}")
        if n_pass < len(fail7):
            for idx, ol, target in results:
                if ol != target:
                    # Compute orbit decomposition
                    bump_m = make_bump_table(m_val)
                    visited = set()
                    orbits = []
                    for sv in range(m_val**3):
                        if sv not in visited:
                            v = sv
                            olen = 0
                            while v not in visited:
                                visited.add(v)
                                olen += 1
                                d = lifted_direction(cycles[idx], v, m_val)
                                v = bump_m[v][d]
                            orbits.append(olen)
                    orbits.sort(reverse=True)
                    print(f"    idx={idx}: orbit={ol}, decomp={orbits[:5]}...")


def compare_boundaries(cycles, pass7, fail7):
    """Compare boundary entries of generalizable vs failing cycles with same interior."""
    print("\n" + "=" * 60)
    print("BOUNDARY COMPARISON: SAME INTERIOR, DIFFERENT OUTCOME")
    print("=" * 60)

    # Group all m=5 passing cycles by interior type
    all_m5_passers = pass7 | fail7

    interior_groups = defaultdict(lambda: {'pass': [], 'fail': []})
    for idx in all_m5_passers:
        ist = interior_subtable(cycles[idx])
        if idx in pass7:
            interior_groups[ist]['pass'].append(idx)
        else:
            interior_groups[ist]['fail'].append(idx)

    # Focus on interior types that have both passing and failing cycles
    for ist, groups in sorted(interior_groups.items(), key=lambda x: len(x[1]['fail']), reverse=True):
        if not groups['fail']:
            continue

        print(f"\n--- Interior: {ist} ---")
        print(f"  Generalizable: {len(groups['pass'])}, Failing: {len(groups['fail'])}")

        # Print boundary tables for all failures
        print("\n  FAILING boundary tables:")
        for idx in sorted(groups['fail']):
            t = table_as_sij(cycles[idx])
            s0 = tuple(t[(0, i, j)] for i in range(3) for j in range(3))
            s2 = tuple(t[(2, i, j)] for i in range(3) for j in range(3))
            print(f"    idx={idx}: s0={s0}, sm1={s2}")

        # Print boundary tables for ALL passing cycles (to see the pattern)
        print(f"\n  PASSING boundary tables ({len(groups['pass'])} cycles):")
        # Group passing by (s0, s2) to see how many distinct boundary combos
        boundary_combos = defaultdict(list)
        for idx in groups['pass']:
            t = table_as_sij(cycles[idx])
            s0 = tuple(t[(0, i, j)] for i in range(3) for j in range(3))
            s2 = tuple(t[(2, i, j)] for i in range(3) for j in range(3))
            boundary_combos[(s0, s2)].append(idx)

        for (s0, s2), members in sorted(boundary_combos.items()):
            print(f"    s0={s0}, sm1={s2}  ({len(members)} cycles)")


def analyze_boundary_structure(cycles, fail7):
    """Look at structural properties of boundary tables."""
    print("\n" + "=" * 60)
    print("STRUCTURAL PROPERTIES OF BOUNDARY TABLES")
    print("=" * 60)

    for idx in sorted(fail7):
        t = table_as_sij(cycles[idx])

        # Check if s=0 table is constant (same direction for all (i,j))
        s0_dirs = set(t[(0, i, j)] for i in range(3) for j in range(3))
        s2_dirs = set(t[(2, i, j)] for i in range(3) for j in range(3))
        s0_const = len(s0_dirs) == 1
        s2_const = len(s2_dirs) == 1

        # Check if s=0 table depends only on i or only on j
        s0_dep_i = all(t[(0, i, 0)] == t[(0, i, 1)] == t[(0, i, 2)] for i in range(3))
        s0_dep_j = all(t[(0, 0, j)] == t[(0, 1, j)] == t[(0, 2, j)] for j in range(3))
        s2_dep_i = all(t[(2, i, 0)] == t[(2, i, 1)] == t[(2, i, 2)] for i in range(3))
        s2_dep_j = all(t[(2, 0, j)] == t[(2, 1, j)] == t[(2, 2, j)] for j in range(3))

        # Interior properties
        ist = interior_subtable(cycles[idx])
        s1_dep_i = all(t[(1, i, 0)] == t[(1, i, 1)] == t[(1, i, 2)] for i in range(3))
        s1_dep_j = all(t[(1, 0, j)] == t[(1, 1, j)] == t[(1, 2, j)] for j in range(3))

        print(f"\n  idx={idx}:")
        print(f"    s0: const={s0_const}, dep_i_only={s0_dep_i and not s0_const}, dep_j_only={s0_dep_j and not s0_const}")
        print(f"    s1: dep_i_only={s1_dep_i}, dep_j_only={s1_dep_j}")
        print(f"    s2: const={s2_const}, dep_i_only={s2_dep_i and not s2_const}, dep_j_only={s2_dep_j and not s2_const}")

        # Check if boundary values 0 and 2 get same direction in each table
        s0_02_same = all(t[(0, 0, j)] == t[(0, 2, j)] for j in range(3)) and all(t[(0, i, 0)] == t[(0, i, 2)] for i in range(3))
        s2_02_same = all(t[(2, 0, j)] == t[(2, 2, j)] for j in range(3)) and all(t[(2, i, 0)] == t[(2, i, 2)] for i in range(3))
        s1_02_i_same = all(t[(1, 0, j)] == t[(1, 2, j)] for j in range(3))
        s1_02_j_same = all(t[(1, i, 0)] == t[(1, i, 2)] for i in range(3))

        print(f"    s1: i_bar=0 and i_bar=2 same dirs: {s1_02_i_same}")
        print(f"    s1: j_bar=0 and j_bar=2 same dirs: {s1_02_j_same}")


def analyze_m_step_algebraically(cycles, pass7, fail7):
    """
    Compute the m-step map for specific cycles at multiple m values
    and look for algebraic patterns.
    """
    print("\n" + "=" * 60)
    print("ALGEBRAIC M-STEP MAP ANALYSIS")
    print("=" * 60)

    # Focus on interior type (0,2,0,0,2,0,0,2,0)
    target_interior = (0, 2, 0, 0, 2, 0, 0, 2, 0)

    fail_indices = [idx for idx in fail7 if interior_subtable(cycles[idx]) == target_interior]
    pass_indices = [idx for idx in pass7 if interior_subtable(cycles[idx]) == target_interior]

    print(f"\nInterior type: {target_interior}")
    print(f"Failing: {len(fail_indices)}, Passing: {len(pass_indices)}")

    # For one failing and one passing cycle, compute detailed m-step maps
    for label, idx in [("FAIL", fail_indices[0]), ("PASS", pass_indices[0])]:
        t = table_as_sij(cycles[idx])
        s0 = tuple(t[(0, i, j)] for i in range(3) for j in range(3))
        s2 = tuple(t[(2, i, j)] for i in range(3) for j in range(3))
        print(f"\n  [{label}] idx={idx}, s0={s0}, sm1={s2}")

        for m_val in [5, 7, 9]:
            m_step = compute_m_step_map(cycles[idx], m_val)

            print(f"\n    m={m_val} m-step map:")
            # Print the map organized by coarsened regions
            for ci in range(3):
                for cj in range(3):
                    region_maps = []
                    for I in range(m_val):
                        for J in range(m_val):
                            if coarsen(I, m_val) == ci and coarsen(J, m_val) == cj:
                                I2, J2 = m_step[(I, J)]
                                dI = (I2 - I) % m_val
                                dJ = (J2 - J) % m_val
                                region_maps.append(((I, J), (I2, J2), (dI, dJ)))
                    if region_maps:
                        deltas = set(r[2] for r in region_maps)
                        if len(deltas) == 1:
                            d = deltas.pop()
                            print(f"      ci={ci}, cj={cj}: uniform delta=({d[0]}, {d[1]}) [{len(region_maps)} vertices]")
                        else:
                            print(f"      ci={ci}, cj={cj}: NONUNIFORM [{len(region_maps)} vertices]")
                            for (I, J), (I2, J2), (dI, dJ) in region_maps:
                                print(f"        ({I},{J}) -> ({I2},{J2}) delta=({dI},{dJ})")


def analyze_orbit_structure_at_m7(cycles, fail7):
    """Detailed orbit analysis at m=7 for the 16 failures."""
    print("\n" + "=" * 60)
    print("ORBIT STRUCTURE AT m=7 FOR FAILURES")
    print("=" * 60)

    m = 7
    for idx in sorted(fail7):
        m_step = compute_m_step_map(cycles[idx], m)

        # Find all orbits of the m-step map
        visited = set()
        orbits = []
        for I in range(m):
            for J in range(m):
                if (I, J) not in visited:
                    orbit = []
                    v = (I, J)
                    while v not in visited:
                        visited.add(v)
                        orbit.append(v)
                        v = m_step[v]
                    orbits.append(orbit)

        print(f"\n  idx={idx}: {len(orbits)} orbits, lengths={[len(o) for o in orbits]}")
        for oi, orbit in enumerate(orbits):
            # Show first few elements and the coarsened regions visited
            regions_visited = set()
            for (I, J) in orbit:
                regions_visited.add((coarsen(I, m), coarsen(J, m)))
            print(f"    Orbit {oi} (len {len(orbit)}): starts at {orbit[0]}, regions={sorted(regions_visited)}")


def check_degenerate_interior_property(cycles, pass7, fail7):
    """
    Check if the 16 failures share a specific property:
    the interior table has boundary values (coarsen=0 and coarsen=2) mapped to the same direction.
    """
    print("\n" + "=" * 60)
    print("DEGENERATE INTERIOR PROPERTY CHECK")
    print("=" * 60)

    all_m5_passers = pass7 | fail7

    for idx in sorted(all_m5_passers):
        ist = interior_subtable(cycles[idx])
        # Check: do coarsen=0 and coarsen=2 get the same direction for each row?
        # Interior table: ist[3*i + j] = direction at (i_bar, j_bar)
        # i_bar=0 and i_bar=2 rows:
        row0 = tuple(ist[0*3+j] for j in range(3))  # i_bar=0
        row2 = tuple(ist[2*3+j] for j in range(3))  # i_bar=2
        i_degenerate = (row0 == row2)

        # j_bar=0 and j_bar=2 columns:
        col0 = tuple(ist[i*3+0] for i in range(3))  # j_bar=0
        col2 = tuple(ist[i*3+2] for i in range(3))  # j_bar=2
        j_degenerate = (col0 == col2)

        if idx in fail7:
            print(f"  FAIL idx={idx}: i_degenerate={i_degenerate}, j_degenerate={j_degenerate}, interior={ist}")

    # Count this property among generalizable cycles
    n_either = 0
    n_both = 0
    for idx in pass7:
        ist = interior_subtable(cycles[idx])
        row0 = tuple(ist[0*3+j] for j in range(3))
        row2 = tuple(ist[2*3+j] for j in range(3))
        i_deg = (row0 == row2)
        col0 = tuple(ist[i*3+0] for i in range(3))
        col2 = tuple(ist[i*3+2] for i in range(3))
        j_deg = (col0 == col2)
        if i_deg or j_deg:
            n_either += 1
        if i_deg and j_deg:
            n_both += 1
    print(f"\n  Among 996 generalizable: {n_either} have i OR j degenerate interior, {n_both} have BOTH")


def check_permutation_property(cycles, pass7, fail7):
    """
    Check if at the boundary tables (s=0, s=m-1), the failing cycles have
    a 'non-permuting' structure that the passing ones avoid.

    Specifically: does the boundary table at s=0 or s=m-1 fail to be a
    bijection when restricted to certain coordinates?
    """
    print("\n" + "=" * 60)
    print("BOUNDARY TABLE SYMMETRY ANALYSIS")
    print("=" * 60)

    all_m5 = pass7 | fail7

    for idx in sorted(fail7):
        t = table_as_sij(cycles[idx])

        # For each s_bar, check if the table depends on i only, j only, both, or neither
        for s in [0, 2]:
            entries = {}
            for i in range(3):
                for j in range(3):
                    entries[(i,j)] = t[(s, i, j)]

            # Does it depend on i only?
            i_only = all(entries[(i,0)] == entries[(i,1)] == entries[(i,2)] for i in range(3))
            # Does it depend on j only?
            j_only = all(entries[(0,j)] == entries[(1,j)] == entries[(2,j)] for j in range(3))
            # Is it constant?
            const = len(set(entries.values())) == 1

            s_label = "s=0" if s == 0 else "s=m-1"
            vals = [entries[(i,j)] for i in range(3) for j in range(3)]
            dir_counts = {d: vals.count(d) for d in range(3)}

            print(f"  FAIL idx={idx}, {s_label}: const={const}, i_only={i_only}, j_only={j_only}, dir_counts={dir_counts}")


def find_necessary_condition(cycles, pass7, fail7):
    """
    Try to find a simple necessary condition for generalizability
    that the 16 failures violate.
    """
    print("\n" + "=" * 60)
    print("SEARCHING FOR NECESSARY CONDITIONS")
    print("=" * 60)

    all_m5 = pass7 | fail7

    # Hypothesis: for each s_bar layer, the direction table should use
    # all 3 directions with specific multiplicity
    print("\nDirection multiplicity in each layer:")
    for idx in sorted(fail7)[:4]:
        t = table_as_sij(cycles[idx])
        for s in range(3):
            dirs = [t[(s, i, j)] for i in range(3) for j in range(3)]
            counts = tuple(sorted([dirs.count(d) for d in range(3)]))
            print(f"  FAIL idx={idx}, s={s}: dir counts={counts}")

    print()
    for idx in sorted(pass7)[:4]:
        t = table_as_sij(cycles[idx])
        for s in range(3):
            dirs = [t[(s, i, j)] for i in range(3) for j in range(3)]
            counts = tuple(sorted([dirs.count(d) for d in range(3)]))
            print(f"  PASS idx={idx}, s={s}: dir counts={counts}")

    # Check if failures have any layer that uses only 2 directions
    print("\nLayers with < 3 distinct directions:")
    fail_has_2dir = 0
    pass_has_2dir = 0
    for idx in fail7:
        t = table_as_sij(cycles[idx])
        for s in range(3):
            dirs = set(t[(s, i, j)] for i in range(3) for j in range(3))
            if len(dirs) < 3:
                fail_has_2dir += 1
                break
    for idx in pass7:
        t = table_as_sij(cycles[idx])
        for s in range(3):
            dirs = set(t[(s, i, j)] for i in range(3) for j in range(3))
            if len(dirs) < 3:
                pass_has_2dir += 1
                break
    print(f"  Failures with a 2-dir layer: {fail_has_2dir}/16")
    print(f"  Passers with a 2-dir layer: {pass_has_2dir}/996")

    # Check: does ANY layer use only 1 direction?
    fail_has_1dir = 0
    pass_has_1dir = 0
    for idx in fail7:
        t = table_as_sij(cycles[idx])
        for s in range(3):
            dirs = set(t[(s, i, j)] for i in range(3) for j in range(3))
            if len(dirs) == 1:
                fail_has_1dir += 1
                break
    for idx in pass7:
        t = table_as_sij(cycles[idx])
        for s in range(3):
            dirs = set(t[(s, i, j)] for i in range(3) for j in range(3))
            if len(dirs) == 1:
                pass_has_1dir += 1
                break
    print(f"  Failures with a 1-dir layer: {fail_has_1dir}/16")
    print(f"  Passers with a 1-dir layer: {pass_has_1dir}/996")

    # Count how many layers are constant (all same direction)
    print("\nNumber of constant layers per cycle:")
    fail_const_counts = defaultdict(int)
    pass_const_counts = defaultdict(int)
    for idx in fail7:
        t = table_as_sij(cycles[idx])
        n_const = sum(1 for s in range(3) if len(set(t[(s,i,j)] for i in range(3) for j in range(3))) == 1)
        fail_const_counts[n_const] += 1
    for idx in pass7:
        t = table_as_sij(cycles[idx])
        n_const = sum(1 for s in range(3) if len(set(t[(s,i,j)] for i in range(3) for j in range(3))) == 1)
        pass_const_counts[n_const] += 1
    print(f"  Failures: {dict(fail_const_counts)}")
    print(f"  Passers: {dict(pass_const_counts)}")

    # NEW: Check if the "full table" treats coarsen=0 and coarsen=2 identically
    # across ALL three layers
    print("\nFull table degeneracy (coarsen=0 ↔ coarsen=2 identical):")
    fail_full_deg = 0
    pass_full_deg = 0
    for idx in fail7:
        t = table_as_sij(cycles[idx])
        # Check i-degeneracy: T(s,0,j) == T(s,2,j) for all s,j
        i_deg = all(t[(s,0,j)] == t[(s,2,j)] for s in range(3) for j in range(3))
        # Check j-degeneracy: T(s,i,0) == T(s,i,2) for all s,i
        j_deg = all(t[(s,i,0)] == t[(s,i,2)] for s in range(3) for i in range(3))
        if i_deg or j_deg:
            fail_full_deg += 1
            print(f"    FAIL idx={idx}: i_deg={i_deg}, j_deg={j_deg}")
    for idx in pass7:
        t = table_as_sij(cycles[idx])
        i_deg = all(t[(s,0,j)] == t[(s,2,j)] for s in range(3) for j in range(3))
        j_deg = all(t[(s,i,0)] == t[(s,i,2)] for s in range(3) for i in range(3))
        if i_deg or j_deg:
            pass_full_deg += 1
    print(f"  Failures with full degeneracy: {fail_full_deg}/16")
    print(f"  Passers with full degeneracy: {pass_full_deg}/996")


def main():
    cycles, pass5, pass7, fail7 = classify_all_cycles()

    test_failures_extended(cycles, fail7)
    compare_boundaries(cycles, pass7, fail7)
    analyze_boundary_structure(cycles, fail7)
    check_degenerate_interior_property(cycles, pass7, fail7)
    analyze_orbit_structure_at_m7(cycles, fail7)
    check_permutation_property(cycles, pass7, fail7)
    find_necessary_condition(cycles, pass7, fail7)
    analyze_m_step_algebraically(cycles, pass7, fail7)

if __name__ == "__main__":
    main()
