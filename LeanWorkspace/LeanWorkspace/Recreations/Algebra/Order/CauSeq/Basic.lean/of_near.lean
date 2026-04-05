import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem of_near (f : ℕ → β) (g : CauSeq β abv) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - g j) < ε) :
    IsCauSeq abv f
  | ε, ε0 =>
    let ⟨i, hi⟩ := exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (CauSeq.cauchy₃ g <| half_pos ε0)
    ⟨i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := hi _ le_rfl; rw [abv_sub abv] at h₁
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij))
      rwa [add_halves, add_halves, add_right_comm, sub_add_sub_cancel, sub_add_sub_cancel] at this⟩

