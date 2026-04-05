import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

theorem intrinsicStar_comp' (f : E →ₗ[R] F) (g : G →ₗ[R] E) :
    star (toConv (f ∘ₗ g)) = toConv ((star (toConv f)).ofConv ∘ₗ (star (toConv g)).ofConv) := by
  simpa using LinearMap.intrinsicStar_comp _ _

