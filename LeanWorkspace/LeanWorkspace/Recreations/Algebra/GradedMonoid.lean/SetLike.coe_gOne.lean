import Mathlib

variable {ι : Type*}

variable {R : Type*}

theorem SetLike.coe_gOne {S : Type*} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => A i) _ _) = (1 : R) := rfl

