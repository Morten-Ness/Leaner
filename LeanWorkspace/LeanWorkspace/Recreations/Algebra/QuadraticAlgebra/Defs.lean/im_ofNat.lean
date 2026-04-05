import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [AddCommMonoidWithOne R]

theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : QuadraticAlgebra R a b).im = 0 := rfl

