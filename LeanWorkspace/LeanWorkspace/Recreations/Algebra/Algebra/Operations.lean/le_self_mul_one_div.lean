import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem le_self_mul_one_div {I : Submodule R A} (hI : I ≤ 1) : I ≤ I * (1 / I) := by
  simpa using mul_le_mul_right (Submodule.one_le_one_div.mpr hI) _

