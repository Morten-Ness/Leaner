import Mathlib

variable (R : Type*) [Zero R] [One R] [Neg R]

private theorem pow_four [Infinite R] : #R ^ 4 = #R := power_nat_eq (aleph0_le_mk R) <| by decide


theorem mk_quaternion : #(ℍ[R]) = #R ^ 4 := Cardinal.mk_quaternionAlgebra _ _ _

