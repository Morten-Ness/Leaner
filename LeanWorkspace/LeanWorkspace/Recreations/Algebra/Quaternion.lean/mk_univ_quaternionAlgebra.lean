import Mathlib

variable {R : Type*} (c₁ c₂ c₃ : R)

private theorem pow_four [Infinite R] : #R ^ 4 = #R := power_nat_eq (aleph0_le_mk R) <| by decide


theorem mk_univ_quaternionAlgebra : #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_univ, Cardinal.mk_quaternionAlgebra]

