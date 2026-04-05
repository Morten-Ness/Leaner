import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]

theorem intrinsicStar_smulRight [Module S F] [StarModule S F] (f : WithConv (E →ₗ[S] S)) (x : F) :
    star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x)) := by
  ext; simp

