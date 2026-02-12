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

#check Nat.lt_wfRel
#check (Nat.succ_le_succ (Nat.zero_le 0))

#check Nat.eq_or_lt_of_le

namespace WellFounded

variable {α : Sort u}
variable {motive : α → Sort v}
variable (h : α → Nat)
variable (F : (x : α) → ((y : α) → InvImage (· < ·) h y x → motive y) → motive x)

/-- Helper gadget that prevents reduction of `Nat.eager n` unless `n` evalutes to a ground term. -/
def Nat.eager (n : Nat) : Nat :=
  if Nat.beq n n = true then n else n

theorem Nat.eager_eq (n : Nat) : Nat.eager n = n := ite_self n

theorem Nat.le_of_lt_add_one {n m : Nat} : n < m + 1 → n ≤ m := Nat.le_of_succ_le_succ

protected theorem Nat.lt_add_one (n : Nat) : LT.lt n (HAdd.hAdd n 1) := Nat.le_refl (Nat.succ n)

/--
A well-founded fixpoint operator specialized for `Nat`-valued measures. Given a measure `h`, it expects
its higher order function argument `F` to invoke its argument only on values `y` that are smaller
than `x` with regard to `h`.

In contrast to to `WellFounded.fix`, this fixpoint operator reduces on closed terms. (More precisely:
when `h x` evalutes to a ground value)

-/
def Nat.fix : (x : α) → motive x :=
  let rec go : ∀ (fuel : Nat) (x : α), (h x < fuel) → motive x :=
    fun fuel x hfuel ↦
     match fuel with
     | Nat.zero => (Nat.not_succ_le_zero _ hfuel).elim
     | Nat.succ f' => F x (fun y hy => go f' y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_add_one hfuel)))
  fun x => go (Nat.eager (h x + 1)) x (Nat.eager_eq _ ▸ Nat.lt_add_one _)


#print Nat.brecOn

end WellFounded

def minus3'' : Nat → List Nat :=
WellFounded.Nat.fix (fun x ↦ x) fun a a_1 ↦
  (match (motive := (x : Nat) → ((y : Nat) → InvImage (fun x1 x2 ↦ x1 < x2) (fun x ↦ x) y x → List Nat) → List Nat)
      a with
    | 0 => fun x ↦ []
    | Nat.succ n => fun x ↦ (n + 1) :: x (n - 2) sorry)
    a_1

#check minus3

#reduce minus3'' 200
