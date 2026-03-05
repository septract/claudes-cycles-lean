#!/usr/bin/env python3
"""
Test the hypothesis: the 16 failures fail iff m ≡ 1 mod 3 (and m > 3, m odd).
Also verify the orbit decomposition pattern.
"""
from enumerate import (
    enumerate_ham_cycles, orbit_length, is_hamiltonian, interior_subtable
)

def main():
    print("Enumerating cycles...")
    cycles = enumerate_ham_cycles()

    # Identify the 16 failures
    print("Identifying the 16 failures (pass m=5, fail m=7)...")
    pass5 = set()
    for i, c in enumerate(cycles):
        if is_hamiltonian(c, 5):
            pass5.add(i)

    fail7 = set()
    for i in pass5:
        if not is_hamiltonian(cycles[i], 7):
            fail7.add(i)

    print(f"Found {len(fail7)} failures")

    # Test at m = 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31
    test_ms = [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 37, 43, 49]
    # Filter to odd values
    test_ms = [m for m in test_ms if m % 2 == 1]

    print(f"\n{'m':>4} {'m%3':>4} {'m%6':>4} {'pass':>6} {'fail':>6} {'orbit_decomp (1st failure)':>40}")
    print("-" * 80)

    for m_val in test_ms:
        n_pass = 0
        n_fail = 0
        first_fail_decomp = None
        for idx in sorted(fail7):
            ol = orbit_length(cycles[idx], m_val)
            if ol == m_val ** 3:
                n_pass += 1
            else:
                n_fail += 1
                if first_fail_decomp is None:
                    # Quick orbit decomposition via m-step map
                    from enumerate import compute_m_step_map, coarsen
                    m_step = compute_m_step_map(cycles[idx], m_val)
                    visited = set()
                    orbits = []
                    for I in range(m_val):
                        for J in range(m_val):
                            if (I, J) not in visited:
                                v = (I, J)
                                olen = 0
                                while v not in visited:
                                    visited.add(v)
                                    olen += 1
                                    v = m_step[v]
                                orbits.append(olen)
                    orbits.sort(reverse=True)
                    first_fail_decomp = str(orbits[:5])

        decomp_str = first_fail_decomp or "N/A"
        print(f"{m_val:>4} {m_val%3:>4} {m_val%6:>4} {n_pass:>6} {n_fail:>6} {decomp_str:>40}")

    # If the pattern holds, verify the orbit decomposition formula
    print("\n\nORBIT DECOMPOSITION PATTERN VERIFICATION")
    print("=" * 60)
    print("Hypothesis: at m ≡ 1 mod 3, orbits are [(m²+2)/3, (m²+2)/3, (m²-4)/3]")
    for m_val in [7, 13, 19, 25, 31, 37, 43, 49]:
        if m_val % 3 != 1:
            continue
        n1 = (m_val**2 + 2) // 3
        n2 = (m_val**2 - 4) // 3
        ok = (m_val**2 + 2) % 3 == 0 and (m_val**2 - 4) % 3 == 0
        print(f"  m={m_val}: n1={(m_val**2+2)/3:.1f}, n2={(m_val**2-4)/3:.1f}, integer={ok}, 2*n1+n2={2*n1+n2}, m²={m_val**2}")

    # Check: for the 996 generalizable cycles, do ALL pass at m ≡ 1 mod 3?
    print("\n\nVERIFICATION: 996 generalizable cycles at m=19 (≡ 1 mod 3)")
    pass7 = pass5 - fail7
    n_pass_19 = 0
    for idx in pass7:
        if is_hamiltonian(cycles[idx], 19):
            n_pass_19 += 1
    print(f"  Pass m=19: {n_pass_19}/{len(pass7)}")

if __name__ == "__main__":
    main()
