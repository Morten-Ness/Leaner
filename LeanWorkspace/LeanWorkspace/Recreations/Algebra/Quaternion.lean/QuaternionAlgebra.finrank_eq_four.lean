import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [Module.finrank, QuaternionAlgebra.rank_eq_four, Cardinal.toNat_ofNat]

