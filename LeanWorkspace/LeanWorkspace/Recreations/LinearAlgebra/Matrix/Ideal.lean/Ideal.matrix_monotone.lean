import Mathlib

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

theorem matrix_monotone : Monotone (Ideal.matrix (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)

