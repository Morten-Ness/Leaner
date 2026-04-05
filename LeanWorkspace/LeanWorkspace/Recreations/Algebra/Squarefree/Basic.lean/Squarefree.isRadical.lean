import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [DecompositionMonoid R]

theorem Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x := (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb

