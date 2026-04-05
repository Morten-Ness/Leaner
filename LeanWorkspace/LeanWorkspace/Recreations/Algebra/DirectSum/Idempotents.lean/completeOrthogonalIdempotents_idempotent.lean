import Mathlib

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

set_option backward.isDefEq.respectTransparency false in
theorem completeOrthogonalIdempotents_idempotent [Fintype I] :
    CompleteOrthogonalIdempotents (DirectSum.idempotent V) where
  idem := DirectSum.isIdempotentElem_idempotent V
  ortho i j hij := by
    simp only
    rw [← DirectSum.decompose_eq_mul_idempotent, DirectSum.idempotent, decompose_coe,
      of_eq_of_ne (h := hij.symm), Submodule.coe_zero]
  complete := by
    apply (decompose V).injective
    refine DFunLike.ext _ _ fun i ↦ ?_
    rw [decompose_sum, DFinsupp.finset_sum_apply]
    simp [DirectSum.idempotent, of_apply]

