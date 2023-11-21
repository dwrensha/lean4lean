import Lean4Lean.Reduce

variable {α : Type uu} (r : α → α → Prop) [DecidableRel r]

local infixl:50 " ≼ " => r

def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l

/-- `insertionSort l` returns `l` sorted using the insertion sort algorithm. -/
def insertionSort : List α → List α
  | [] => []
  | b :: l => orderedInsert r b (insertionSort l)

#check insertionSort

--#l4lreduce insertionSort (·≤·) [5, 2,3]


def split : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := split l
    (a :: l₂, l₁)

theorem split_cons_of_eq (a : α) {l l₁ l₂ : List α} (h : split l = (l₁, l₂)) :
    split (a :: l) = (a :: l₂, l₁) := by rw [split, h]

theorem length_split_le :
    ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → l₁.length ≤ l.length ∧ l₂.length ≤ l.length
  | [], _, _, rfl => ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | a :: l, l₁', l₂', h => by
    sorry
/-    cases' e : split l with l₁ l₂
    injection (split_cons_of_eq _ e).symm.trans h; substs l₁' l₂'
    cases' length_split_le e with h₁ h₂
    exact ⟨Nat.succ_le_succ h₂, Nat.le_succ_of_le h₁⟩-/

theorem length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
    List.length l₁ < (a :: b :: l).length ∧ l₂.length < (a :: b :: l).length := by
  sorry
/-
  cases e : split l with l₁' l₂'
  injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h; substs l₁ l₂
  cases' length_split_le e with h₁ h₂
  exact ⟨Nat.succ_le_succ (Nat.succ_le_succ h₁), Nat.succ_le_succ (Nat.succ_le_succ h₂)⟩ -/

def merge : List α → List α → List α
  | [], l' => l'
  | l, [] => l
  | a :: l, b :: l' => if a ≼ b then a :: merge l (b :: l') else b :: merge (a :: l) l'
  termination_by merge l₁ l₂ => List.length l₁ + List.length l₂

def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l => by
    -- Porting note: rewrote to make `mergeSort_cons_cons` proof easier
    let ls := (split (a :: b :: l))
    have e : split (a :: b :: l) = ⟨ls.1, ls.2⟩ := rfl
    have h := length_split_lt e
    have := h.1
    have := h.2
    exact merge r (mergeSort ls.1) (mergeSort ls.2)
  termination_by mergeSort l => List.length l

--#l4lreduce mergeSort (·≤·) [5]
