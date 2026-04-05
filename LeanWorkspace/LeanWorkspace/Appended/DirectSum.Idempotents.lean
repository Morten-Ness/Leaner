import Mathlib

section

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

end

section

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

theorem decompose_eq_mul_idempotent (x : R) (i : I) : decompose V x i = x * DirectSum.idempotent V i := by
  rw [← smul_eq_mul (a := x), DirectSum.idempotent, ← Submodule.coe_smul, ← smul_apply, ← decompose_smul,
    smul_eq_mul, mul_one]

end

section

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

theorem isIdempotentElem_idempotent (i : I) : IsIdempotentElem (DirectSum.idempotent V i : R) := by
  rw [IsIdempotentElem, ← DirectSum.decompose_eq_mul_idempotent, DirectSum.idempotent, decompose_coe, of_eq_same]

end
