import Mathlib

open scoped DirectSum

variable {M : Type*} {ι : Type*} {R : Type*}

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

theorem decomposeAux_eq_decompose :
    ⇑(AddMonoidAlgebra.decomposeAux f : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i) =
      DirectSum.decompose (gradeBy R f) := rfl

