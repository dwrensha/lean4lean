import Std.Data.Array.Lemmas
import Std.Data.HashMap.Basic

theorem funext_iff {β : α → Sort u} {f₁ f₂ : ∀ x : α, β x} : f₁ = f₂ ↔ ∀ a, f₁ a = f₂ a :=
  Iff.intro (fun h _ ↦ h ▸ rfl) funext

protected theorem Nat.le_iff_exists_add {a b : Nat} : a ≤ b ↔ ∃ c, b = a + c :=
  ⟨fun h => ⟨_, (Nat.add_sub_cancel' h).symm⟩, fun ⟨_, h⟩ => h ▸ Nat.le_add_right ..⟩

protected theorem Nat.le_iff_exists_add' {a b : Nat} : a ≤ b ↔ ∃ c, b = c + a := by
  simp [Nat.add_comm, Nat.le_iff_exists_add]

protected theorem List.Forall₂.rfl
    {R : α → α → Prop} {l : List α} (h : ∀ a ∈ l, R a a) : l.Forall₂ R l := by
  induction l with
  | nil => constructor
  | cons _ _ ih => simp at h; exact .cons h.1 (ih h.2)

@[simp] theorem List.forall₂_nil_left_iff {l} : Forall₂ R nil l ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

@[simp] theorem List.forall₂_nil_right_iff {l} : Forall₂ R l nil ↔ l = nil :=
  ⟨fun H => by cases H; rfl, by rintro rfl; exact Forall₂.nil⟩

theorem List.forall₂_cons_left_iff {a l u} :
    Forall₂ R (a :: l) u ↔ ∃ b u', R a b ∧ Forall₂ R l u' ∧ u = b :: u' :=
  Iff.intro
    (fun h => match u, h with | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    (fun h => match u, h with | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂)

theorem List.forall₂_cons_right_iff {b l u} :
    Forall₂ R u (b :: l) ↔ ∃ a u', R a b ∧ Forall₂ R u' l ∧ u = a :: u' :=
  Iff.intro
    (fun h => match u, h with | b :: u', Forall₂.cons h₁ h₂ => ⟨b, u', h₁, h₂, rfl⟩)
    (fun h => match u, h with | _, ⟨_, _, h₁, h₂, rfl⟩ => Forall₂.cons h₁ h₂)

theorem List.Forall₂.imp (H : ∀ a b, R a b → S a b)
    {l₁ l₂} (h : Forall₂ R l₁ l₂) : Forall₂ S l₁ l₂ := by
  induction h <;> constructor <;> [(apply H; assumption); assumption]

@[simp] theorem List.forall₂_map_left_iff {f : γ → α} :
    ∀ {l u}, Forall₂ R (map f l) u ↔ Forall₂ (fun c b => R (f c) b) l u
  | [], _ => by simp only [map, forall₂_nil_left_iff]
  | a :: l, _ => by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]

@[simp] theorem List.forall₂_map_right_iff {f : γ → β} :
    ∀ {l u}, Forall₂ R l (map f u) ↔ Forall₂ (fun a c => R a (f c)) l u
  | _, [] => by simp only [map, forall₂_nil_right_iff]
  | _, b :: u => by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]

theorem List.Forall₂.length_eq : ∀ {l₁ l₂}, Forall₂ R l₁ l₂ → length l₁ = length l₂
  | _, _, Forall₂.nil => rfl
  | _, _, Forall₂.cons _ h₂ => congrArg Nat.succ (Forall₂.length_eq h₂)

theorem List.map_id' {f : α → α} (l : List α) (h : ∀ x ∈ l, f x = x) : map f l = l := by
  induction l <;> simp_all

def List.All (P : α → Prop) : List α → Prop
  | [] => True
  | a::as => P a ∧ as.All P

theorem List.All.imp {P Q : α → Prop} (h : ∀ a, P a → Q a) : ∀ {l : List α}, l.All P → l.All Q
  | [] => id
  | _::_ => And.imp (h _) (List.All.imp h)

instance [BEq α] [LawfulBEq α] : PartialEquivBEq α where
  symm h := by simp at *; exact h.symm
  trans h1 h2 := by simp at *; exact h1.trans h2

instance [BEq α] [LawfulBEq α] [Hashable α] : Std.HashMap.LawfulHashable α where
  hash_eq h := by simp at *; subst h; rfl

instance : LawfulBEq Lean.FVarId where
  eq_of_beq := @fun ⟨a⟩ ⟨b⟩ h => by cases LawfulBEq.eq_of_beq (α := Lean.Name) h; rfl
  rfl := LawfulBEq.rfl (α := Lean.Name)

theorem beq_comm [BEq α] [PartialEquivBEq α] (a b : α) : (a == b) = (b == a) :=
  Bool.eq_iff_iff.2 ⟨PartialEquivBEq.symm, PartialEquivBEq.symm⟩

theorem Array.get_modify {arr : Array α} {x i} (h : i < arr.size) :
    (arr.modify x f).get ⟨i, by simp [h]⟩ =
    if x = i then f (arr.get ⟨i, h⟩) else arr.get ⟨i, h⟩ := by
  simp [modify, modifyM, Id.run]; split
  · simp [get_set _ _ _ h]; split <;> simp [*]
  · rw [if_neg (mt (by rintro rfl; exact h) ‹_›)]
