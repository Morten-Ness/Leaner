import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

theorem GradesBy.decompose_single (m : M) (r : R) :
    DirectSum.decompose (gradeBy R f) (Finsupp.single m r : R[M]) =
      DirectSum.of (fun i : ι => gradeBy R f i) (f m)
        ⟨Finsupp.single m r, AddMonoidAlgebra.single_mem_gradeBy _ _ _⟩ := AddMonoidAlgebra.decomposeAux_single _ _ _

