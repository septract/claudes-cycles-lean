/-
# TCB Analysis for Claude's Cycles

Uses lean-tcb to identify the Trusted Computing Base for the main theorem.
The TCB is the set of definitions an auditor must manually review to trust
the theorem's correctness — everything else is verified by Lean's kernel.

With the existential formulation, the construction (direction, fiber, step)
is a witness in the proof, not part of the statement, so it's kernel-verified
and excluded from the TCB.
-/
import ClaudesCycles.Main
import LeanTcb

set_option tcb.checkAnnotations true

namespace ClaudesCycles

-- Analyze the main theorem's TCB
#tcb claudes_cycles_decomposition

-- Show the dependency tree
#tcb_tree claudes_cycles_decomposition

end ClaudesCycles
