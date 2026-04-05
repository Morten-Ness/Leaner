import Mathlib

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

theorem matrix_top : (⊤ : Ideal R).matrix n = ⊤ := by
  ext; simp

