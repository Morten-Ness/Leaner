import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

theorem decomposeAux_single (m : M) (r : R) :
    AddMonoidAlgebra.decomposeAux f (Finsupp.single m r) =
      DirectSum.of (fun i : ι => gradeBy R f i) (f m)
        ⟨Finsupp.single m r, AddMonoidAlgebra.single_mem_gradeBy _ _ _⟩ := by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl

