namespace WellFounded


section helpers

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

end helpers

/--
A well-founded fixpoint operator specialized for `Nat`-valued measures. Given a measure `h`, it expects
its higher order function argument `F` to invoke its argument only on values `y` that are smaller
than `x` with regard to `h`.

In contrast to to `WellFounded.fix`, this fixpoint operator reduces on closed terms. (More precisely:
when `h x` evalutes to a ground value)

-/
def Nat.fix {α : Sort u} {motive : α → Sort v}
    (h : α → Nat)
    (x : α)
    (F : (x : α) → ((y : α) → InvImage (· < ·) h y x → motive y) → motive x) :
    motive x :=
  let rec go : ∀ (fuel : Nat) (x : α), (h x < fuel) → motive x := fun fuel x hfuel ↦
    match fuel with
    | Nat.zero => (Nat.not_succ_le_zero _ hfuel).elim
    | Nat.succ f' => F x (fun y hy => go f' y (Nat.lt_of_lt_of_le hy (Nat.le_of_lt_add_one hfuel)))
  go (Nat.eager (h x + 1)) x (Nat.eager_eq _ ▸ Nat.lt_add_one _)

end WellFounded
