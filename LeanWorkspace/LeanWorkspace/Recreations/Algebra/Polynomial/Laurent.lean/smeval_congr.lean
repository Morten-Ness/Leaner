import Mathlib

variable {R S : Type*}

variable [Semiring R] [AddCommMonoid S] [SMulWithZero R S] [Monoid S] (f g : R[T;T⁻¹]) (x y : Sˣ)

theorem smeval_congr : f = g → x = y → f.smeval x = g.smeval y := by rintro rfl rfl; rfl

