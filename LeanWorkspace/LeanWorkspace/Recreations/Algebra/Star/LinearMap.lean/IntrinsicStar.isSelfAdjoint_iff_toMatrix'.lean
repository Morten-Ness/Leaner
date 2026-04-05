import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

theorem IntrinsicStar.isSelfAdjoint_iff_toMatrix' (f : WithConv ((m → R) →ₗ[R] (n → R))) :
    IsSelfAdjoint f ↔ ∀ i j, IsSelfAdjoint (f.ofConv.toMatrix' i j) := by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, ← Matrix.ext_iff,
    WithConv.ext_iff]

