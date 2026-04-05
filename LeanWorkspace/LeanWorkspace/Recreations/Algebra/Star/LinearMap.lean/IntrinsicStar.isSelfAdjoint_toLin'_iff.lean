import Mathlib

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

theorem IntrinsicStar.isSelfAdjoint_toLin'_iff (A : Matrix n m R) :
    IsSelfAdjoint (toConv A.toLin') ↔ ∀ i j, IsSelfAdjoint (A i j) := by
  simp [IsSelfAdjoint, Matrix.intrinsicStar_toLin', ← ext_iff]

