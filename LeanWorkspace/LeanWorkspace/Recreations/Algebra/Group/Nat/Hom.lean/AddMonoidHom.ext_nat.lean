import Mathlib

variable {M : Type*}

variable {A B F : Type*} [FunLike F ℕ A]

theorem AddMonoidHom.ext_nat [AddZeroClass A] {f g : ℕ →+ A} : f 1 = g 1 → f = g := ext_nat' f g

