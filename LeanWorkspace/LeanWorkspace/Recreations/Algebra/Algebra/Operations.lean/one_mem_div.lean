import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem one_mem_div {I J : Submodule R A} : 1 ∈ I / J ↔ J ≤ I := by
  rw [← Submodule.one_le, Submodule.le_div_iff_mul_le, Submodule.one_mul]

