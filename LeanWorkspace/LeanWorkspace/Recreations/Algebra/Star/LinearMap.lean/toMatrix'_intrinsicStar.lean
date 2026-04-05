import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

theorem toMatrix'_intrinsicStar (f : WithConv ((m → R) →ₗ[R] (n → R))) :
    (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star := by
  ext; simp

