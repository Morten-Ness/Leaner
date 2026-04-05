import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

theorem leadingCoeff_single [Nonempty A] (hD : D.Injective) (a : A) (r : R) :
    (single a r).leadingCoeff D = r := by
  classical
  rw [AddMonoidAlgebra.leadingCoeff, AddMonoidAlgebra.supDegree_single]
  split_ifs with hr
  · simp [hr]
  · rw [Function.leftInverse_invFun hD, single_apply, if_pos rfl]

