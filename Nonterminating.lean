import Lean4Lean.Reduce

def tautext {A B : Prop} (a : A) (b : B)
: A = B := propext (Iff.intro (λ _ => b) (λ _ => a))
def True' : Prop := ∀ A : Prop, A → A
def delta : True' → True' := λ z : True' => z _  id z
def omega : True' := λ _ a => cast (tautext id a) delta
def Omega : True' := delta omega --non-terminating term

def f (h : True ∧ True) : Nat := And.rec (motive := fun _ => Nat) (fun _ _ => 1) h
example : f (id ⟨.intro,.intro⟩) = 1 := rfl --recursor reduces here

--set_option pp.proofs true in
--#l4lreduce f (Omega _ ⟨.intro,.intro⟩)
