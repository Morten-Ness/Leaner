import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem le_of_exists {f g : CauSeq α abs} (h : ∃ i, ∀ j ≥ i, f j ≤ g j) : f ≤ g := let ⟨i, hi⟩ := h
  (or_assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨_, hK0, j, hKj⟩ := hgf
      not_lt_of_ge (hi (max i j) (le_max_left _ _))
        (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _)))))

