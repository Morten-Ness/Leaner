import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

theorem intrinsicStar_comp (f : WithConv (E →ₗ[R] F)) (g : WithConv (G →ₗ[R] E)) :
    star (toConv (f.ofConv ∘ₗ g.ofConv)) = toConv ((star f).ofConv ∘ₗ (star g).ofConv) := by
  ext; simp

