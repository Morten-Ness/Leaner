import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem toGL_inj (g g' : Matrix.SpecialLinearGroup n R) :
    (g : GeneralLinearGroup n R) = g' ↔ g = g' := Matrix.SpecialLinearGroup.toGL_injective.eq_iff

