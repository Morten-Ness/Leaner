import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem isIdempotentElem_toSubmodule (S : Subalgebra R A) :
    IsIdempotentElem S.toSubmodule := by
  apply le_antisymm
  · refine (Subalgebra.mul_toSubmodule_le _ _).trans_eq ?_
    rw [sup_idem]
  · intro x hx1
    rw [← mul_one x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) ∈ S from one_mem S)

