import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable {l m n : Type*} {R α : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Fintype n] [AddCommMonoid α] (i j : n) (c : α)

theorem trace_single_mul [NonUnitalNonAssocSemiring R] [Fintype m]
    (i : n) (j : m) (a : R) (x : Matrix m n R) :
    (single i j a * x).trace = a • x j i := by
  simp [Matrix.trace, mul_apply, single, ite_and]

