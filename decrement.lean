import Std
import Lean4Lean.Reduce

def minus3' : Nat → List Nat
| 0 => []
| n + 1 => (n + 1) :: minus3' (n - 2)
decreasing_by exact Nat.sub_lt_succ n 2

--set_option maxHeartbeats 0 in
--#reduce minus3' 10

def minus3 : Nat → List Nat :=
fun n ↦
 Acc.rec
  (fun x _hx ih ↦ match x with
                | 0 => []
                | m + 1 => (m + 1) :: (ih (m - 2) (Nat.sub_lt_succ m 2)))
  (WellFounded.apply Nat.lt_wfRel.wf n)

-- This builds a very large term. Try increasing the numeral!
--#reduce (WellFounded.apply Nat.lt_wfRel.wf 4)

--set_option maxRecDepth 4000 in
--set_option maxHeartbeats 0 in
--#l4lreduce minus3 20
