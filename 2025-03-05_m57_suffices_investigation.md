# Investigation Brief: Does checking m=3,5,7 suffice for generalizability?

Created: 2025-03-05

## The Claim

Knuth's paper (p.4, lines 195-197) states:

> "It turns out that there are exactly 11502 Hamiltonian cycles for m = 3, of which exactly 1012 generalize to Hamiltonian cycles for m = 5. Furthermore, exactly 996 of them generalize to Hamiltonian cycles for both m = 5 and m = 7. And those 996 are in fact generalizable to all odd m > 1."

The claim "those 996 are in fact generalizable to all odd m > 1" is **asserted without proof**. It was verified computationally by Filip Stappers up to m = 101. Your task is to investigate whether this claim can be proved, and if so, how.

## Setup

A "Claude-like" cycle at general odd m is determined by a 9-entry table T(s_bar, i_bar, j_bar) -> direction, where s_bar, i_bar, j_bar in {0, 1, 2} are "coarsened" values:

```
coarsen(x) = 0  if x = 0
           = 2  if x = m-1
           = 1  otherwise (0 < x < m-1)
```

At m=3, coarsen is the identity on {0,1,2}, so every m=3 Hamiltonian cycle determines a unique 9-entry table. The cycle is "generalizable" if the lifted cycle (using this table at general m) is Hamiltonian for all odd m >= 3.

## What the lifted cycle looks like

At general odd m, the step function visits all m fibers (s=0, 1, ..., m-1) in round-robin order. One "round" of m steps consists of:

1. **Fiber 0** (s=0): 1 step using table entries with s_bar=0
2. **Interior fibers** (s=1, ..., m-2): m-2 steps, ALL using entries with s_bar=1
3. **Fiber m-1** (s=m-1): 1 step using entries with s_bar=2

The m-step map (one full round) takes a fiber-0 vertex to the next fiber-0 vertex. Hamiltonicity requires this map, iterated m^2 times, to visit all m^2 fiber-0 vertices.

## Why this is subtle

During the m-2 interior steps, the orbit bumps one coordinate at each step. Which coordinate depends on the coarsened values of i and j. But **i and j can cross coarsened boundaries during interior traversal**:

- Example: if the interior rule bumps j, then j eventually reaches m-1 (coarsened from 1 to 2), changing which rule applies
- The number of boundary crossings depends on m

For Claude's specific cycle 0, this isn't a problem: i never changes during interior traversal (only j or k gets bumped), and the interior rule depends only on coarsened i (not j). But for the other 993 generalizable cycles, the interior dynamics may be more complex.

## Key parameters that vary with m

At each fiber type, the table entry determines which coordinate to bump based on (coarsened i, coarsened j). During interior traversal:

- **m=3**: 1 interior step. No boundary crossing possible.
- **m=5**: 3 interior steps. i or j might cross one boundary (from "interior" to "m-1" or from "0" to "interior").
- **m=7**: 5 interior steps. More crossings possible.
- **General m**: m-2 interior steps.

The question: does the qualitative behavior stabilize at m=7? Specifically, does the interior orbit pattern (which coarsened regions i and j visit, in what order) become independent of m for m >= 7?

## Investigation tasks

### Task 1: Classify interior dynamics

For each of the 9 possible interior rules (s_bar=1 entries), determine the orbit of (coarsened_i, coarsened_j) under iterated application. There are 3^9 = 19683 possible interior sub-tables, but many are equivalent. Classify them by:

- Which coordinates change (just i? just j? both? k via fiber?)
- Whether i or j can cross coarsened boundaries
- The asymptotic behavior (what happens as m -> infinity?)

### Task 2: Analyze the m-step map

For a given 9-entry table, the m-step map (fiber-0 to fiber-0) is:

```
M(i,j) = [fiber-0 step] o [interior^(m-2)] o [fiber-(m-1) step](i,j)
```

where coordinates are tracked mod m. Determine:

- Is M always an affine map on (ZMod m)^2? (i.e., M(i,j) = (i + a, j + b) for some a, b depending on the table and possibly on coarsened regions?)
- If not affine globally, is it piecewise-affine with a structure that stabilizes for large m?

### Task 3: Why m=7 might be the threshold

Hypothesis: for m >= 7, the interior traversal always passes through the same sequence of coarsened regions (regardless of m), because:

- With 5+ interior steps, every possible boundary crossing pattern that will ever occur already occurs at m=7
- The "extra" interior steps for m > 7 are all in the (coarsened_i=1, coarsened_j=1) region, contributing a uniform linear shift

If true, this means the m-step map for m >= 7 has the form:

```
M_m(i,j) = M_7(i,j) + (m-7) * delta
```

where delta is the per-step increment in the (1,1) interior region. Since delta involves advancing one coordinate by 1, the orbit structure depends on gcd(delta_component, m), which is 1 for odd m (if delta_component = +/-2 or +/-1 with the right parity).

### Task 4: Check the 16 cycles that fail at m=5 but work at m=3

There are 11502 - 1012 = 10490 cycles that don't generalize to m=5, plus 1012 - 996 = 16 that work at m=5 but fail at m=7. The 16 are particularly interesting: what goes wrong at m=7 that doesn't go wrong at m=5? Understanding these failure modes helps understand what m=7 tests that m=5 doesn't.

### Task 5: Attempt a proof sketch

If the analysis supports it, sketch a proof of: "For any 9-entry Claude-like cycle table, if the lifted cycle is Hamiltonian at m=3, m=5, and m=7, then it is Hamiltonian at all odd m >= 3."

The proof would likely go:
1. Classify the 996 tables into a finite number of "orbit structure" families
2. For each family, show the m-step map has the right properties
3. The key property is that some coordinate advances by an amount coprime to m

## Relevant files in the codebase

- `paper/claude-cycles.txt` — Knuth's paper (full text)
- `ClaudesCycles/ClaudeLike.lean` — `coarsen`, `ClaudeLikeTable`, `claudeLikeDir`, `claudeLikeStep`, `IsValidTable`, `IsGeneralizable`
- `ClaudesCycles/Orbit.lean` — `IsHamiltonian`, `ZMod.addOrderOf_two`, `orbit_add_two_surj`
- `ClaudesCycles/Cycle0.lean` — Complete proof for Claude's cycle 0 (example of the fiber-by-fiber argument)
- `ClaudesCycles/Cycle1.lean` — Complete proof for cycle 1
- `ClaudesCycles/Cycle2.lean` — Complete proof for cycle 2

## Computational results (verified by `compute/enumerate_cycles.py`)

All of Knuth's counts are confirmed:
- 11502 Hamiltonian cycles at m=3
- 1012 generalize to m=5
- 996 generalize to both m=5 and m=7
- 996 also generalize to m=9, 11, 13 (all 996 pass every tested m)
- 4554 unordered decompositions at m=3
- 760 generalizable decompositions

### The 16 cycles that fail at m=7

All 16 cycles that generalize to m=5 but NOT m=7 have orbit length exactly **119 = 7 x 17** at m=7 (need 343 = 7^3). Note 343/119 is not an integer, so there are multiple orbits of different lengths.

### Interior pattern classification (KEY FINDING)

The 996 generalizable cycles have only **17 distinct interior patterns** (the 9-entry sub-table for s_bar=1). Entries indexed by (i_bar, j_bar) with i_bar, j_bar in {0,1,2}:

| Interior pattern | Count | Depends on | Description |
|-----------------|-------|------------|-------------|
| (0,0,0,0,0,0,0,0,0) | 122 | neither | Always bump i |
| (1,1,1,1,1,1,1,1,1) | 122 | neither | Always bump j |
| (2,2,2,2,2,2,2,2,2) | 24 | neither | Always bump k |
| (0,0,2,0,0,2,0,0,2) | 76 | j only | Bump i unless j=m-1, then bump k |
| (1,1,1,1,1,1,2,2,2) | 76 | i only | Bump j unless i=m-1, then bump k |
| (2,2,2,1,1,1,1,1,1) | 76 | i only | Bump k if i=0, else bump j |
| (2,0,0,2,0,0,2,0,0) | 76 | j only | Bump k if j=0, else bump i |
| (0,2,0,0,2,0,0,2,0) | 59 | j only | Bump k if j=1... (complex) |
| (1,1,1,2,2,2,1,1,1) | 59 | i only | Bump j if i!=1, bump k if i=1 |
| (0,2,2,0,2,2,0,2,2) | 57 | j only | Bump i if j=0, else bump k |
| (1,1,1,2,2,2,2,2,2) | 57 | i only | Bump j if i=0, else bump k |
| (2,2,2,2,2,2,1,1,1) | 57 | i only | Bump k if i!=m-1, else bump j |
| (2,2,0,2,2,0,2,2,0) | 57 | j only | Bump k if j!=m-1, else bump i |
| (2,2,2,1,1,1,2,2,2) | 35 | i only | Bump k if i!=1, bump j if i=1 |
| (2,0,2,2,0,2,2,0,2) | 35 | j only | Bump k if j!=1, bump i if j=1 |
| (0,2,1,0,2,2,1,1,0) | 4 | BOTH i,j | Complex |
| (1,1,0,2,2,0,0,2,1) | 4 | BOTH i,j | Complex |

**Critical insight:** 15 of 17 patterns depend on at most ONE coarsened coordinate (i or j). For these, the "other" coordinate is stable during interior traversal, making the m-step analysis clean — the behavior is identical for all m >= 3. Only 8 cycles (2 patterns) have complex interior dynamics depending on both i and j.

This suggests the proof could proceed:
1. For "depends on i only" patterns: i is stable during interior, j (or k) advances by m-2
2. For "depends on j only" patterns: j is stable during interior, i (or k) advances by m-2
3. For "depends on neither" patterns: one coordinate advances by m-2, trivial
4. For the 8 complex cycles: need careful case analysis

## Computational tools

You can write and run Python/Lean code. For the enumeration:

- The m=3 digraph has 27 vertices. Use (i,j,k) in {0,1,2}^3.
- At each vertex, the 3 arcs go to (i+1,j,k), (i,j+1,k), (i,j,k+1) mod 3.
- A Hamiltonian cycle selects one arc per vertex; the cycle visits all 27 vertices.
- The "lifted" version at m=5 or m=7 uses the coarsened table.

Write Python to enumerate cycles and test generalizability. Focus on understanding the 16 cycles that work at m=5 but fail at m=7.

## Success criteria

- Enumerate the 11502, 1012, 996 numbers and confirm them
- Characterize what makes the 16 "m=5 but not m=7" cycles fail
- Determine whether the "m=7 suffices" claim is provable by a structural argument
- If so, sketch the proof at a level of detail suitable for Lean formalization
