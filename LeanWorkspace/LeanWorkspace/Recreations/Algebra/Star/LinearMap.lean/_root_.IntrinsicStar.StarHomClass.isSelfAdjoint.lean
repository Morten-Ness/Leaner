import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

theorem _root_.IntrinsicStar.StarHomClass.isSelfAdjoint {S : Type*} [FunLike S E F]
    [LinearMapClass S R E F] [StarHomClass S E F] {f : S} :
    IsSelfAdjoint (toConv (f : E →ₗ[R] F) : WithConv (E →ₗ[R] F)) := LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr (map_star f)

