# Integrating Aristotle (Harmonic) Proofs into the Project

Notes for future agents on what changes are needed when an Aristotle-generated proof arrives.

## Context

Aristotle (https://aristotle.harmonic.fun) generates self-contained Lean 4 files that redefine all project definitions locally and import Mathlib directly. To integrate into our project (which has its own `Defs.lean`, `Basic.lean`, `Orbit.lean` infrastructure), several mechanical translations are needed.

The Cycle 2 proof (project ID `6cd583d5-681c-47c7-b76d-b1092a5086bc`) had 3 issues preventing compilation, plus needed structural changes for integration.

## Compilation Fixes (applied to standalone file first)

### 1. Harmonic's custom `generalize_proofs` tactic (~200 lines)

Aristotle prepends a custom reimplementation of the `generalize_proofs` tactic that opens the deprecated `Mathlib.Tactic.GeneralizeProofs` namespace. This causes:
```
unknown namespace 'Mathlib.Tactic.GeneralizeProofs'
```
**Fix:** Delete the entire block (look for the comment `-- Harmonic generalize_proofs tactic` or the large tactic definition). The standard `generalize_proofs` from `import Mathlib.Tactic` works fine. Add this comment to prevent Aristotle reinserting it:
```
-- Harmonic `generalize_proofs` tactic
```

### 2. Heartbeat timeout on `step_pow_m_eq_F`

The lemma `step_pow_m_eq_F` uses brute-force `rcases m` + `simp +zetaDelta` that exceeds the default 200K heartbeat limit.
**Fix:** Add `set_option maxHeartbeats 800000 in` before the lemma.

### 3. `exact?` search tactics

Aristotle leaves `exact?` calls that work but are slow. Replace with the concrete terms the LSP suggests (use `lean_code_actions` on the line). One example: `exact?` resolved to `exact Function.iterate_cancel_of_add h_inj this`.

## Integration Changes (standalone → project imports)

### Drop redefinitions

Aristotle redefines `Vertex`, `bump`, `fiber`, `direction`, `step`, `IsHamiltonian` locally. Delete all of these — the project provides them via `import ClaudesCycles.Orbit`.

### Name translations

Aristotle uses fully qualified names. Within `namespace ClaudesCycles`:

| Aristotle | Project |
|-----------|---------|
| `ClaudesCycles.step m 2` | `step m 2` |
| `ClaudesCycles.fiber m` | `fiber m` |
| `ClaudesCycles.bump m` | `bump m` |
| `ClaudesCycles.direction m` | `direction m` |
| `ClaudesCycles.ClaudesCycles.F` | `F` |

The double namespace (`ClaudesCycles.ClaudesCycles.F`) is an artifact of Aristotle defining `def ClaudesCycles.F` inside `namespace ClaudesCycles`.

### Replace redundant lemmas with project equivalents

Aristotle reproves things the project already has. Key substitutions:

| Aristotle lemma | Project equivalent | Arg order change |
|---|---|---|
| `ClaudesCycles.step_fiber m v 2` | `fiber_step m 2 v` | `(m, v, c)` → `(m, c, v)` |
| `ClaudesCycles.iterate_step_fiber m k v` | `iterate_fiber m 2 v k` | `(m, k, v)` → `(m, c, v, k)` |
| inline `Function.Injective (step m 2)` proof | `step_injective m 2` | direct use |

### Imports

Add `import Mathlib.Tactic` for `grind`, `linear_combination'`, `nlinarith` which aren't transitively available from `ClaudesCycles.Orbit`.

### Structural

- Wrap helper lemmas in `noncomputable section` / `end` (the `F` definition needs it).
- Remove `skip` no-op placeholders that Aristotle inserts.
- Remove trivial wrapper lemmas (e.g., `cycle2_minimalPeriod_dvd_m3` which just calls `cycle2_hamiltonian_fiber_zero`).
