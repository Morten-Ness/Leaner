import Mathlib

variable {R : Type*} [NonUnitalSemiring R]

theorem isQuasiregular_iff' {x : R} : IsQuasiregular x ↔ IsUnit (PreQuasiregular.equiv x) := by
  simp only [IsQuasiregular, IsUnit, Equiv.apply_symm_apply,
    ← PreQuasiregular.equiv (R := R).injective.eq_iff]

