import Mathlib

variable {R : Type*} (c₁ c₂ c₃ : R)

private theorem pow_four [Infinite R] : #R ^ 4 = #R := power_nat_eq (aleph0_le_mk R) <| by decide


theorem mk_quaternionAlgebra : #(ℍ[R,c₁,c₂,c₃]) = #R ^ 4 := by
  rw [mk_congr (QuaternionAlgebra.equivProd c₁ c₂ c₃)]
  simp only [mk_prod, lift_id]
  ring

