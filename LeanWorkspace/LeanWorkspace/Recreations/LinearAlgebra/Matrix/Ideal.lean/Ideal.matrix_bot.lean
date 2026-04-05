import Mathlib

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

theorem matrix_bot : (⊥ : Ideal R).matrix n = ⊥ := by
  ext M
  simp only [Ideal.mem_matrix, mem_bot]
  constructor
  · intro H; ext; apply H
  · intro H; simp [H]

