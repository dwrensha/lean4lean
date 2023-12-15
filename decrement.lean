import Std
import Lean4Lean.Reduce

def minus3 : Nat → Nat
| 0 => 0
| n + 1 => minus3 (n - 2)
decreasing_by exact Nat.sub_lt_succ n 2

--set_option maxHeartbeats 0 in
--#l4lreduce minus3 7
