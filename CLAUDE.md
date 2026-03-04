# Claude's Cycles — Lean 4 Formalization

Development guide for the Lean 4 formalization of [*Claude's Cycles*](https://cs.stanford.edu/~knuth/papers/claude-cycles.pdf) (Don Knuth, February 2026). The paper proves that a certain digraph on $(\mathbb{Z}/m\mathbb{Z})^3$ can be decomposed into three directed Hamiltonian cycles for all odd $m \ge 3$. The construction was discovered by Claude Opus 4.6.

Reference text is also available at `paper/claude-cycles.txt` (gitignored).

## The Mathematical Problem

**Digraph.** Vertices are triples $(i, j, k) \in (\mathbb{Z}/m\mathbb{Z})^3$. Each vertex has exactly three outgoing arcs, corresponding to incrementing one coordinate mod $m$:
- Arc 0: $(i, j, k) \to (i{+}1, j, k)$
- Arc 1: $(i, j, k) \to (i, j{+}1, k)$
- Arc 2: $(i, j, k) \to (i, j, k{+}1)$

**Goal.** Decompose the $3m^3$ arcs into three directed Hamiltonian cycles (each of length $m^3$), for all odd $m \ge 3$.

## Claude's Construction

Define the **fiber index** $s = (i + j + k) \bmod m$. The direction function $d(c, v)$ assigns a permutation of $\{0,1,2\}$ to each vertex; cycle $c$ follows direction $d(c, v)$.

**Cycle 0 ($c = 0$):**
- $s = 0$: bump $i$ if $j = m{-}1$, else bump $k$
- $0 < s < m{-}1$: bump $k$ if $i = m{-}1$, else bump $j$
- $s = m{-}1$: bump $j$ if $i > 0$, else bump $k$

**Cycle 1 ($c = 1$):**
- $s = 0$: bump $j$
- $0 < s < m{-}1$: bump $i$
- $s = m{-}1$, $i > 0$: bump $k$
- $s = m{-}1$, $i = 0$: bump $j$

**Cycle 2 ($c = 2$):**
- $s = 0$, $j < m{-}1$: bump $i$
- $s = 0$, $j = m{-}1$: bump $k$
- $0 < s < m{-}1$, $i < m{-}1$: bump $k$
- $0 < s < m{-}1$, $i = m{-}1$: bump $j$
- $s = m{-}1$: bump $i$

## Proof Strategy

The proof in the paper works fiber-by-fiber. Key observations:

1. **Fiber structure.** All arcs go from fiber $F_s$ to $F_{s+1}$. So each cycle visits fibers in round-robin order: $s=0, s=1, \ldots, s=m{-}1, s=0, \ldots$

2. **For cycle 0:** The first coordinate $i$ changes only when $s = 0$ and $j = m{-}1$. So all $m^2$ vertices sharing a given $i$ appear consecutively. Within each $i$-block, track how $j$ and $k$ evolve to show all $m^2$ pairs $(j,k)$ appear.

3. **The "k advances by 2" argument.** Each time we return to $s = 0$ within an $i$-block, $k$ has advanced by 2 (mod $m$). Since $m$ is odd, $\gcd(2,m) = 1$, so all residues are hit. This is the crux of why odd $m$ works.

4. **The $i = m{-}1$ block** has different behavior (rules change at $s = m{-}1$), handled separately.

5. **Cycles 1 and 2** are proved Hamiltonian by analogous fiber-tracking arguments (see Appendix in the paper).

6. **Arc partition.** Since $d$ assigns a permutation at each vertex, the three cycles automatically use disjoint arcs, and together they cover all $3m^3$ arcs.

## Formalization Structure

```
ClaudesCycles/
  Defs.lean       -- Vertex, bump, fiber, direction, step
  Basic.lean      -- fiber_step, direction_bijective, step_injective/bijective
  Orbit.lean      -- Orbit infrastructure, IsHamiltonian, addOrderOf_two, orbit_add_two_surj
  Cycle0.lean     -- Hamiltonicity of cycle 0 (direction lemmas, i-stability, m-step analysis)
  Cycle1.lean     -- Hamiltonicity of cycle 1
  Cycle2.lean     -- Hamiltonicity of cycle 2
  Main.lean       -- Main decomposition theorem (existential formulation, @[tcb]-annotated)
  Tcb.lean        -- lean-tcb analysis of the Trusted Computing Base
```

### Key Definitions (`Defs.lean`)

- `Vertex m := ZMod m × ZMod m × ZMod m`
- `bump (v : Vertex m) (d : Fin 3) : Vertex m` — increment coordinate $d$ by 1
- `fiber (v : Vertex m) : ZMod m := v.1 + v.2.1 + v.2.2`
- `direction (c : Fin 3) (v : Vertex m) : Fin 3` — which coordinate cycle $c$ bumps at $v$
- `step (c : Fin 3) (v : Vertex m) : Vertex m := bump v (direction c v)`

### Key Lemmas

1. `fiber_step` (`Basic.lean`): `fiber (step c v) = fiber v + 1` — all arcs advance the fiber by 1
2. `direction_bijective` (`Basic.lean`): at each vertex, $c \mapsto d(c, v)$ is a bijection on `Fin 3`
3. `step_injective` / `step_bijective` (`Basic.lean`): `step c` is a permutation of vertices
4. `ZMod.addOrderOf_two` (`Orbit.lean`): $\mathrm{ord}(2) = m$ in $\mathbb{Z}/m\mathbb{Z}$ when $m$ is odd
5. `ZMod.orbit_add_two_surj` (`Orbit.lean`): adding 2 repeatedly from any start covers all of $\mathbb{Z}/m\mathbb{Z}$
6. `cycle{0,1,2}_hamiltonian`: each cycle has minimal period $m^3$ at every vertex
7. `claudes_cycles_decomposition` (`Main.lean`): the main theorem

### Trusted Computing Base

The main theorem uses an existential formulation: the direction function is a *witness* in the proof, not part of the statement. This means the construction is kernel-verified and excluded from the TCB.

The `#tcb` command in `Tcb.lean` reports **5 declarations** to audit (5% of project): `Vertex`, `bump`, `bump.match_1`, `IsHamiltonian`, and the theorem statement itself. The remaining 89 project declarations are outside the TCB. One standard axiom (`Classical.choice`).

### Core Proof Technique for Hamiltonicity

For each cycle, the argument is:
1. Show that vertices within each $i$-block (for cycle 0) or analogous grouping are visited contiguously.
2. Within a block, track the "$s = 0$ return points" to show the secondary coordinate advances by 2 each time.
3. Since $\gcd(2, m) = 1$ for odd $m$, all values are hit, giving $m^2$ vertices per block.
4. Show all $m$ blocks are visited, giving $m \times m^2 = m^3$ total vertices.

The $\gcd(2, m) = 1$ argument is the reason the construction requires odd $m$.

## Lean 4 / Mathlib Conventions

- Use Mathlib's `ZMod` for modular arithmetic.
- Use `Function.Iterate` and `Function.minimalPeriod` for orbit reasoning.
- `Equiv.Perm (Fin 3)` for the permutation property.
- Prefer `omega` and `decide` tactics for concrete numeric goals.
- Use `Fin.val` / `ZMod.val` conversions carefully — these are a common pain point.
- `omega`/`linarith` do not work on `ZMod`; use `add_left_cancel`, `ring`, `push_cast` instead.
- `ZMod.natCast_zmod_val a` gives `(↑a.val : ZMod m) = a`.
- For $s = -1$ direction proofs: `split_ifs <;> simp_all` works when manual `simp` does not.

## Known Difficulties

- **ZMod vs Fin vs Nat:** Modular arithmetic in Lean/Mathlib can be verbose. The formalization uses `ZMod m` throughout, which is natural for the algebra but requires care with casts.
- **Case splits on $s$:** The direction function has $3 \times 3 = 9$ cases per cycle. Tactic proofs use `split_ifs` extensively.
- **The "k advances by 2" induction:** This is an induction on the number of returns to $s = 0$. May need a custom induction principle or well-founded recursion on the orbit length.
- **$m = 1$ edge case:** The theorem assumes $m \ge 3$ and `Odd m`. The $m = 1$ case is trivially true but degenerate.
