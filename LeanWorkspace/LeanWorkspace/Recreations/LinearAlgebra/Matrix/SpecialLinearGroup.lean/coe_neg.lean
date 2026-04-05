import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

variable [Fact (Even (Fintype.card n))]

theorem coe_neg (g : Matrix.SpecialLinearGroup n R) : ↑(-g) = -(g : Matrix n n R) := rfl

