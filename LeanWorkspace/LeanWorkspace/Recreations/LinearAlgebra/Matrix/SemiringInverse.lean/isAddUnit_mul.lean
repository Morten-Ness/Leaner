import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem isAddUnit_mul {d : n → R} (hAB : A * B = diagonal d) (i j k : n) (hij : i ≠ j) :
    IsAddUnit (A i k * B k j) := by
  revert k
  rw [← IsAddUnit.sum_univ_iff, ← mul_apply, hAB, diagonal_apply_ne _ hij]
  exact isAddUnit_zero

