import Mathlib

variable {M : Type*}

theorem isUnit_of_associated_mul [CommMonoidWithZero M] [IsCancelMulZero M] {p b : M}
    (h : Associated (p * b) p) (hp : p ≠ 0) : IsUnit b := by
  obtain ⟨a, ha⟩ := h
  refine .of_mul_eq_one a ((mul_right_inj' hp).mp ?_)
  rwa [← mul_assoc, mul_one]

