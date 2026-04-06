import Mathlib

universe uι u v

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem mul_mem_mul_rev (hm : m ∈ M) (hn : n ∈ N) : n * m ∈ M * N := by
  rw [show M * N = N * M by ext x; simp [Submodule.mul_comm]]
  exact Submodule.mul_mem_mul hn hm
