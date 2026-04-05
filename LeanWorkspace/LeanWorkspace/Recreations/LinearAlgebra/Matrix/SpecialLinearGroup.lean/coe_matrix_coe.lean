import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem coe_matrix_coe (g : Matrix.SpecialLinearGroup n ℤ) :
    ↑(g : Matrix.SpecialLinearGroup n R) = (↑g : Matrix n n ℤ).map (Int.castRingHom R) := map_apply_coe (Int.castRingHom R) g

