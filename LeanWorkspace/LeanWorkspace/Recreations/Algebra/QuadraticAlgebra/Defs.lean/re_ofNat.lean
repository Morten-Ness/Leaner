import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [AddCommMonoidWithOne R]

theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).re = ofNat(n) := rfl

