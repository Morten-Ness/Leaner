import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

theorem intrinsicStar_toLin' (A : Matrix n m R) :
    star (toConv A.toLin') = toConv (A.map star).toLin' := by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, WithConv.ext_iff]

