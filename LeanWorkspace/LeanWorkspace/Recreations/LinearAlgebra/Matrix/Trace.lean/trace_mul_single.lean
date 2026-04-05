import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable {l m n : Type*} {R α : Type*} [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [Fintype n] [AddCommMonoid α] (i j : n) (c : α)

theorem trace_mul_single [NonUnitalNonAssocSemiring R] [Fintype m]
    (x : Matrix m n R) (i : n) (j : m) (a : R) :
    (x * single i j a).trace = MulOpposite.op a • x j i := by
  simp [Matrix.trace, mul_apply, single, ite_and]

