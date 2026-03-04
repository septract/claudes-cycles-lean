/-
# Core Definitions for Claude's Cycles

The digraph on (Z/mZ)³ with arcs that increment one coordinate,
and Claude's direction function decomposing arcs into three Hamiltonian cycles.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Fin
import LeanTcb

namespace ClaudeCycles

variable (m : ℕ) [NeZero m]

/-- A vertex is a triple (i, j, k) in (Z/mZ)³. -/
@[tcb] abbrev Vertex := ZMod m × ZMod m × ZMod m

/-- The three coordinates of a vertex. -/
def Vertex.i (v : Vertex m) : ZMod m := v.1
def Vertex.j (v : Vertex m) : ZMod m := v.2.1
def Vertex.k (v : Vertex m) : ZMod m := v.2.2

/-- Construct a vertex from three coordinates. -/
def Vertex.mk' (i j k : ZMod m) : Vertex m := (i, j, k)

/-- Bump (increment by 1) coordinate d of vertex v.
  d = 0 bumps i, d = 1 bumps j, d = 2 bumps k. -/
@[tcb] def bump (v : Vertex m) (d : Fin 3) : Vertex m :=
  match d with
  | 0 => (v.1 + 1, v.2.1, v.2.2)
  | 1 => (v.1, v.2.1 + 1, v.2.2)
  | 2 => (v.1, v.2.1, v.2.2 + 1)

/-- The fiber index s = i + j + k (mod m). -/
def fiber (v : Vertex m) : ZMod m := v.1 + v.2.1 + v.2.2

/-- The direction function for Claude's cycle decomposition.
  For cycle c at vertex v, returns which coordinate (0, 1, or 2) to bump.

  Cycle 0:
    s = 0:       j = -1 → bump i (0), else bump k (2)
    0 < s < m-1: i = -1 → bump k (2), else bump j (1)
    s = -1:      i ≠ 0  → bump j (1), else bump k (2)

  Cycle 1:
    s = 0:       bump j (1)
    0 < s < m-1: bump i (0)
    s = -1:      i ≠ 0 → bump k (2), else bump j (1)

  Cycle 2:
    s = 0:       j ≠ -1 → bump i (0), else bump k (2)
    0 < s < m-1: i ≠ -1 → bump k (2), else bump j (1)
    s = -1:      bump i (0)
-/
def direction (c : Fin 3) (v : Vertex m) : Fin 3 :=
  let s := fiber m v
  let i := v.1
  let j := v.2.1
  match c with
  | 0 =>
    if s = 0 then (if j = -1 then 0 else 2)
    else if s = -1 then (if i ≠ 0 then 1 else 2)
    else (if i = -1 then 2 else 1)
  | 1 =>
    if s = 0 then 1
    else if s = -1 then (if i ≠ 0 then 2 else 1)
    else 0
  | 2 =>
    if s = 0 then (if j ≠ -1 then 0 else 2)
    else if s = -1 then 0
    else (if i ≠ -1 then 2 else 1)

/-- Step: follow cycle c one step from vertex v. -/
def step (c : Fin 3) (v : Vertex m) : Vertex m :=
  bump m v (direction m c v)

end ClaudeCycles
