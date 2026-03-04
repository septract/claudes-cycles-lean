/-
# TCB Analysis for Claude's Cycles

Uses lean-tcb to identify the Trusted Computing Base for the main theorem.
The TCB is the set of definitions an auditor must manually review to trust
the theorem's correctness — everything else is verified by Lean's kernel.

With the existential formulation, the construction (direction, fiber, step)
is a witness in the proof, not part of the statement, so it's kernel-verified
and excluded from the TCB.
-/
import ClaudeCycles.Main
import LeanTcb

set_option tcb.checkAnnotations true

namespace ClaudeCycles

-- Analyze the main theorem's TCB
#tcb claude_cycles_decomposition

-- Show the dependency tree
#tcb_tree claude_cycles_decomposition

end ClaudeCycles
