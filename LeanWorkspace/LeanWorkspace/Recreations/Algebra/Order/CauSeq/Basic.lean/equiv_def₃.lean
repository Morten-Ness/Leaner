import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem equiv_def₃ {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - g j) < ε := (exists_forall_ge_and (h _ <| half_pos ε0) (CauSeq.cauchy₃ f <| half_pos ε0)).imp fun _ H j ij k jk => by
    let ⟨h₁, h₂⟩ := H _ ij
    have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk))
    rwa [sub_add_sub_cancel', add_halves] at this

