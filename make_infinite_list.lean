import Std
import Lean4Lean.Reduce
import Lean4Lean.Natfix

def make_infinite_list : Nat → List Nat
| .zero => []
| .succ n  => n.succ :: make_infinite_list n.succ
decreasing_by sorry

--set_option pp.proofs true in
--#reduce make_infinite_list 5
