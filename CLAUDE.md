# Claude Cycles — Lean 4 Formalization

Formalization of the proof in `claude-cycles.pdf` (Don Knuth, February 2026) that a certain digraph on (Z/mZ)^3 can be decomposed into three directed Hamiltonian cycles for all odd m >= 3. The construction was discovered by Claude Opus 4.6.

Reference text is also available at `paper/claude-cycles.txt` (gitignored).

## The Mathematical Problem

**Digraph.** Vertices are triples (i, j, k) in (Z/mZ)^3. Each vertex has exactly three outgoing arcs, corresponding to incrementing one coordinate mod m:
- Arc 0: (i, j, k) -> (i+1, j, k)
- Arc 1: (i, j, k) -> (i, j+1, k)
- Arc 2: (i, j, k) -> (i, j, k+1)

**Goal.** Decompose the 3m^3 arcs into three directed Hamiltonian cycles (each of length m^3), for all odd m >= 3.

## Claude's Construction

Define the **fiber index** s = (i + j + k) mod m. The direction function d(i, j, k, c) assigns a permutation of {0,1,2} to each vertex; cycle c follows direction d[c].

**Cycle 0 (c = 0):** The permutation at each vertex is:
- s = 0: if j = m-1 then (0,1,2) else (2,1,0)
- 0 < s < m-1: if i = m-1 then (2,0,1) else (1,0,2)
- s = m-1: if i > 0 then (1,2,0) else (2,1,0)

In words for cycle 0:
- s = 0: bump i if j = m-1, else bump k
- 0 < s < m-1: bump k if i = m-1, else bump j
- s = m-1: bump j if i > 0, else bump k

**Cycle 1 (c = 1):**
- s = 0: bump j
- 0 < s < m-1: bump i
- s = m-1, i > 0: bump k
- s = m-1, i = 0: bump j

**Cycle 2 (c = 2):**
- s = 0, j < m-1: bump i
- s = 0, j = m-1: bump k
- 0 < s < m-1, i < m-1: bump k
- 0 < s < m-1, i = m-1: bump j
- s = m-1: bump i

## Proof Strategy

The proof in the paper works fiber-by-fiber. Key observations:

1. **Fiber structure.** All arcs go from fiber F_s to F_{s+1}. So the cycle visits fibers in round-robin order: s=0, s=1, ..., s=m-1, s=0, ...

2. **For cycle 0:** The first coordinate i changes only when s = 0 and j = m-1. So all m^2 vertices sharing a given i appear consecutively. Within each i-block, track how j and k evolve to show all m^2 pairs (j,k) appear.

3. **The "k advances by 2" argument.** Each time we return to s = 0 within an i-block, k has advanced by 2 (mod m). Since m is odd, gcd(2,m) = 1, so all residues are hit. This is the crux of why odd m works.

4. **The i = m-1 block** has different behavior (rules change at s = m-1), handled separately.

5. **Cycles 1 and 2** are proved Hamiltonian by analogous fiber-tracking arguments (see Appendix in the paper).

6. **Arc partition.** Since d assigns a permutation at each vertex, the three cycles automatically use disjoint arcs, and together they cover all 3m^3 arcs.

## Recommended Formalization Structure

```
ClaudesCycles/
  Basic.lean          -- ZMod m, vertex type, arc type, digraph definition
  Direction.lean      -- The direction function d and its permutation property
  Fiber.lean          -- Fiber decomposition: s = (i+j+k) mod m, layering lemma
  Cycle0.lean         -- Proof that cycle 0 is Hamiltonian
  Cycle1.lean         -- Proof that cycle 1 is Hamiltonian
  Cycle2.lean         -- Proof that cycle 2 is Hamiltonian
  Decomposition.lean  -- Main theorem: valid decomposition for all odd m >= 3
```

### Key Lean Definitions Needed

- `Vertex m := ZMod m × ZMod m × ZMod m`
- `bump (v : Vertex m) (d : Fin 3) : Vertex m` — increment coordinate d
- `fiber (v : Vertex m) : ZMod m := v.1 + v.2.1 + v.2.2`
- `direction (c : Fin 3) (v : Vertex m) : Fin 3` — which coordinate cycle c bumps at vertex v
- `step (c : Fin 3) (v : Vertex m) : Vertex m := bump v (direction c v)`
- `orbit (c : Fin 3) (v : Vertex m) : List (Vertex m)` or via `Function.Iterate`

### Key Lemmas

1. `fiber_step`: `fiber (step c v) = fiber v + 1` — all arcs advance the fiber by 1
2. `direction_perm`: for each vertex v, the map `c ↦ direction c v` is a permutation of Fin 3
3. `cycle0_hamiltonian`: the orbit of cycle 0 from any starting vertex has length m^3
4. `cycle1_hamiltonian`: same for cycle 1
5. `cycle2_hamiltonian`: same for cycle 2
6. `decomposition_valid`: the three cycles partition all arcs

### Core Proof Technique for Hamiltonicity

For each cycle, the argument is:
1. Show that vertices within each i-block (for cycle 0) or analogous grouping are visited contiguously.
2. Within a block, track the "s = 0 return points" to show the secondary coordinate advances by 2 each time.
3. Since gcd(2, m) = 1 for odd m, all values are hit, giving m^2 vertices per block.
4. Show all m blocks are visited, giving m × m^2 = m^3 total vertices.

The `gcd(2, m) = 1` argument is the reason the construction requires odd m.

## Lean 4 / Mathlib Conventions

- Use Mathlib's `ZMod` for modular arithmetic.
- Use `Finset.univ` and `Finset.card` for counting arguments.
- Use `Function.Iterate` or `Function.periodicPt` for orbit reasoning.
- `Equiv.Perm (Fin 3)` for the permutation property.
- Prefer `omega` and `decide` tactics for concrete numeric goals.
- Use `Fin.val` / `ZMod.val` conversions carefully — these are a common pain point.

## Known Difficulties

- **ZMod vs Fin vs Nat:** Modular arithmetic in Lean/Mathlib can be verbose. Decide early whether to work in `ZMod m` or `Fin m` and stick with it. `ZMod m` is more natural for the algebra but `Fin m` may be easier for decidable computations.
- **Case splits on s:** The direction function has 3 × 3 = 9 cases (for cycle 2, more). Tactic proofs may be long. Consider using `match` or `if`/`else` chains and the `split` tactic.
- **The "k advances by 2" induction:** This is an induction on the number of returns to s = 0. May need a custom induction principle or well-founded recursion on the orbit length.
- **m = 1 edge case:** The statement should probably assume `m ≥ 3` and `m % 2 = 1` (or `Odd m`). Note m = 1 is trivially true but degenerate.
