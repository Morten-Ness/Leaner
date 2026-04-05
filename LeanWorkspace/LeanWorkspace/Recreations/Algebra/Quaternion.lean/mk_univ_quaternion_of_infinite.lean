import Mathlib

variable (R : Type*) [Zero R] [One R] [Neg R]

private theorem pow_four [Infinite R] : #R ^ 4 = #R := power_nat_eq (aleph0_le_mk R) <| by decide


theorem mk_univ_quaternion_of_infinite [Infinite R] : #(Set.univ : Set ℍ[R]) = #R := Cardinal.mk_univ_quaternionAlgebra_of_infinite _ _ _

