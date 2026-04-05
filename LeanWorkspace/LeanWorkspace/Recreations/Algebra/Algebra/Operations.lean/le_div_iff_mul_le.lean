import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem le_div_iff_mul_le {I J K : Submodule R A} : I ≤ J / K ↔ I * K ≤ J := by
  rw [Submodule.le_div_iff, Submodule.mul_le]

