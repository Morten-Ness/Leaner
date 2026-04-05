import Mathlib

variable {R : Type*} (c₁ c₂ c₃ : R)

private theorem pow_four [Infinite R] : #R ^ 4 = #R := power_nat_eq (aleph0_le_mk R) <| by decide


theorem mk_quaternionAlgebra_of_infinite [Infinite R] : #(ℍ[R,c₁,c₂,c₃]) = #R := by
  rw [Cardinal.mk_quaternionAlgebra, pow_four]

