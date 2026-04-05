import Mathlib

variable {R A : Type*}

theorem IsSelfAdjoint.smul_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R]
    [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : IsSelfAdjoint a) : r • a ∈ skewAdjoint A := (star_smul _ _).trans <| (congr_arg₂ _ hr ha).trans <| neg_smul _ _

