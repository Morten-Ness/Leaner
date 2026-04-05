import Mathlib

variable {A M : Type*} [AddGroup A] [DivisionMonoid M]

theorem map_zsmul_eq_zpow (ψ : AddChar A M) (n : ℤ) (a : A) : ψ (n • a) = (ψ a) ^ n := ψ.toMonoidHom.map_zpow a n

