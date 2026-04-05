import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem mul_one_div_le_one {I : Submodule R A} : I * (1 / I) ≤ 1 := by
  rw [Submodule.mul_le]
  intro m hm n hn
  rw [Submodule.mem_div_iff_forall_mul_mem] at hn
  rw [Submodule.mul_comm]
  exact hn m hm

