import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

variable [Fact (Even (Fintype.card n))]

theorem coe_int_neg (g : Matrix.SpecialLinearGroup n ℤ) : ↑(-g) = (-↑g : Matrix.SpecialLinearGroup n R) := Subtype.ext <| (@RingHom.mapMatrix n _ _ _ _ _ _ (Int.castRingHom R)).map_neg ↑g

