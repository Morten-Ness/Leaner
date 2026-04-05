import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem map_intCast_inj [CharZero R] {x y : Matrix.SpecialLinearGroup n ℤ} :
    (x : Matrix.SpecialLinearGroup n R) = y ↔ x = y := Matrix.SpecialLinearGroup.map_intCast_injective.eq_iff

