import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R,c₁,c₂,c₃] = 4 := by
  rw [rank_eq_card_basis (QuaternionAlgebra.basisOneIJK c₁ c₂ c₃), Fintype.card_fin]
  norm_num

