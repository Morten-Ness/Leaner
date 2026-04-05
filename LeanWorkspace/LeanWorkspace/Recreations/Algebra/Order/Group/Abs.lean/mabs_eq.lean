import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_eq (hb : 1 ≤ b) : |a|ₘ = b ↔ a = b ∨ a = b⁻¹ := by
  refine ⟨eq_or_eq_inv_of_mabs_eq, ?_⟩
  rintro (rfl | rfl) <;> simp only [mabs_inv, mabs_of_one_le hb]

