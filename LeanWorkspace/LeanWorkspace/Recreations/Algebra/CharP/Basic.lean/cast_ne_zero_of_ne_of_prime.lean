import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem cast_ne_zero_of_ne_of_prime [Nontrivial R]
    {p q : ℕ} [CharP R p] (hq : q.Prime) (hneq : p ≠ q) : (q : R) ≠ 0 := fun h ↦ by
  rw [cast_eq_zero_iff R p q] at h
  rcases hq.eq_one_or_self_of_dvd _ h with rfl | h
  · exact false_of_nontrivial_of_char_one (R := R)
  · exact hneq h

