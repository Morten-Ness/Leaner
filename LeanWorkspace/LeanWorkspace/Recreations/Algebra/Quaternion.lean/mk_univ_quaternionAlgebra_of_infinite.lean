import Mathlib

variable {R : Type*} (c₁ c₂ c₃ : R)

private theorem pow_four [Infinite R] : #R ^ 4 = #R := power_nat_eq (aleph0_le_mk R) <| by decide


theorem mk_univ_quaternionAlgebra_of_infinite [Infinite R] :
    #(Set.univ : Set ℍ[R,c₁,c₂,c₃]) = #R := by rw [Cardinal.mk_univ_quaternionAlgebra, pow_four]

