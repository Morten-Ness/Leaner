import Mathlib

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem leftMulMatrix_eq_repr_mul (x : S) (i j) : Algebra.leftMulMatrix b x i j = b.repr (x * b j) i := by
  -- This is defeq to just `Algebra.toMatrix_lmul' b x i j`,
  -- but the unfolding goes a lot faster with this explicit `rw`.
  rw [Algebra.leftMulMatrix_apply, Algebra.toMatrix_lmul' b x i j]

