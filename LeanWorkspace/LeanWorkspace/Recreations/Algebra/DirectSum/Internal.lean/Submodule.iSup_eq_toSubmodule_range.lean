import Mathlib

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
    [Algebra S R] (A : ι → Submodule S R) [SetLike.GradedMonoid A] :
    ⨆ i, A i = Subalgebra.toSubmodule (DirectSum.coeAlgHom A).range := (Submodule.iSup_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl

