import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : WithConv (E →ₗ[R] F)) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp_rw [IsSelfAdjoint, WithConv.ext_iff, LinearMap.ext_iff, intrinsicStar_apply,
   star_eq_iff_star_eq, eq_comm]

