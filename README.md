# Claude's Cycles — Lean 4 Formalization

A Lean 4 / Mathlib formalization of the main theorem in [*Claude's Cycles*](https://cs.stanford.edu/~knuth/papers/claude-cycles.pdf) by Donald Knuth (February 2026): for every odd $m \ge 3$, the digraph on $(\mathbb{Z}/m\mathbb{Z})^3$ whose arcs increment a single coordinate can be decomposed into three directed Hamiltonian cycles. The construction was discovered by Claude (Opus 4.6) through a 31-step exploration process documented in the paper.

## The Problem

**Digraph.** The vertex set is the $m^3$ triples $(i, j, k) \in (\mathbb{Z}/m\mathbb{Z})^3$. Each vertex has exactly three outgoing arcs:
- $(i, j, k) \to (i{+}1, j, k)$
- $(i, j, k) \to (i, j{+}1, k)$
- $(i, j, k) \to (i, j, k{+}1)$

**Theorem.** For all odd $m \ge 3$, the $3m^3$ arcs can be partitioned into three directed Hamiltonian cycles, each of length $m^3$.

## The Construction

Define the **fiber index** $s = (i + j + k) \bmod m$. Claude's direction function assigns a permutation of $\{0,1,2\}$ to each vertex; cycle $c$ follows direction $d(c, v)$, which determines which coordinate to increment. The full case analysis (9 cases per cycle, 27 total) is given in the paper and formalized in [`ClaudesCycles/Defs.lean`](ClaudesCycles/Defs.lean).

The proof works fiber-by-fiber. Every arc goes from fiber $F_s$ to $F_{s+1}$, so each cycle visits fibers in round-robin order. The key insight: within each "block" of vertices sharing a stable coordinate, the secondary coordinate advances by 2 at each return to fiber 0. Since $\gcd(2, m) = 1$ for odd $m$, all residues are hit. This is the crux of why odd $m$ works.

## Formalization

The main theorem ([`ClaudesCycles/Main.lean`](ClaudesCycles/Main.lean)):

```lean
theorem claudes_cycles_decomposition (hm : Odd m) (hm3 : 3 ≤ m) :
    ∃ (d : Fin 3 → Vertex m → Fin 3),
      (∀ v : Vertex m, Function.Bijective (fun c : Fin 3 => d c v)) ∧
      (∀ c : Fin 3, IsHamiltonian m (fun v => bump m v (d c v)))
```

This states: there exists a direction function $d$ such that (1) at every vertex, the three cycles bump distinct coordinates (arc partition), and (2) each cycle is Hamiltonian. The witness is Claude's direction function, verified by Lean's kernel.

### File Structure

| File | Contents |
|------|----------|
| [`Defs.lean`](ClaudesCycles/Defs.lean) | Vertex type, `bump`, `fiber`, `direction`, `step` |
| [`Basic.lean`](ClaudesCycles/Basic.lean) | `fiber_step`, `direction_bijective`, `step_injective`, `step_bijective` |
| [`Orbit.lean`](ClaudesCycles/Orbit.lean) | Orbit infrastructure, `IsHamiltonian`, `addOrderOf_two`, `orbit_add_two_surj` |
| [`Cycle0.lean`](ClaudesCycles/Cycle0.lean) | Hamiltonicity of cycle 0 (direction lemmas, i-stability, m-step analysis) |
| [`Cycle1.lean`](ClaudesCycles/Cycle1.lean) | Hamiltonicity of cycle 1 |
| [`Cycle2.lean`](ClaudesCycles/Cycle2.lean) | Hamiltonicity of cycle 2 |
| [`Main.lean`](ClaudesCycles/Main.lean) | Main decomposition theorem |
| [`Tcb.lean`](ClaudesCycles/Tcb.lean) | Trusted Computing Base analysis |

### Trusted Computing Base

The theorem is stated in existential form: it asserts the *existence* of a direction function with the required properties, rather than naming a specific one. This means the construction (the `direction` function, `fiber`, `step`, and all intermediate lemmas) appears only as a *witness* in the proof and is verified by Lean's kernel. It does not need manual auditing.

Using [lean-tcb](https://github.com/OathTech/lean-tcb), the Trusted Computing Base — the set of definitions an auditor must manually review to trust the result — consists of only **5 declarations** (5% of the project):

| Declaration | Kind | Role |
|-------------|------|------|
| `Vertex` | `abbrev` | The vertex type $(\mathbb{Z}/m\mathbb{Z})^3$ |
| `bump` | `def` | Incrementing a coordinate |
| `bump.match_1` | `abbrev` | Match auxiliary for `bump` |
| `IsHamiltonian` | `def` | The Hamiltonicity predicate |
| `claudes_cycles_decomposition` | `theorem` | The theorem statement itself |

The remaining 89 project declarations and 768 library dependencies are outside the TCB — their correctness is guaranteed by Lean's kernel. The proof depends on one standard axiom (`Classical.choice`).

## Building

Requires Lean 4.28.0 and Mathlib.

```sh
# Install elan if needed: https://github.com/leanprover/elan
lake build
```

## References

- D. E. Knuth, [*Claude's Cycles*](https://cs.stanford.edu/~knuth/papers/claude-cycles.pdf), February 2026.
