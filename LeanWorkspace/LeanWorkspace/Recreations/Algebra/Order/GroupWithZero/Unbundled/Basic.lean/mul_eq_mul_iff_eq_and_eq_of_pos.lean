import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [PartialOrder α]

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)

