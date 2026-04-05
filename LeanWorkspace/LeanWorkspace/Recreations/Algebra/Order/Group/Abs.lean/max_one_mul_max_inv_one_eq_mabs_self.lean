import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem max_one_mul_max_inv_one_eq_mabs_self (a : G) : max a 1 * max a⁻¹ 1 = |a|ₘ := by
  symm
  rcases le_total 1 a with (ha | ha) <;> simp [ha]

