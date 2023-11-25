import Std.Data.HashMap.Basic
import Lean4Lean.Reduce

open Std

-- https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/no.20kernel.20reduction.20of.20HashMap.2Einsert/near/403887177

--#eval (HashMap.empty : HashMap Nat Nat).isEmpty  -- true
--#eval (HashMap.empty.insert 1 1).isEmpty  -- false


--set_option maxHeartbeats 0 in
--#l4lreduce (HashMap.empty.insert 1 1).isEmpty

--example : (HashMap.empty : HashMap Nat Nat).isEmpty = true := rfl -- okay
--example : (HashMap.empty.insert 1 1).isEmpty = false := rfl 
