import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem one_le_one_div {I : Submodule R A} : 1 ≤ 1 / I ↔ I ≤ 1 := by
  rw [Submodule.le_div_iff_mul_le, Submodule.one_mul]

