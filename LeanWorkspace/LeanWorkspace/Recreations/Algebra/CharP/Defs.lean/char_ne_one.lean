import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem char_ne_one [Nontrivial R] (p : ℕ) [hc : CharP R p] : p ≠ 1 := fun hp : p = 1 =>
  have : (1 : R) = 0 := by simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero

