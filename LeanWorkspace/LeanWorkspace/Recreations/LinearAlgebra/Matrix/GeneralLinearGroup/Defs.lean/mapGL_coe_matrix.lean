import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem mapGL_coe_matrix (g : Matrix.SpecialLinearGroup n R) :
    ((Matrix.SpecialLinearGroup.mapGL S g) : Matrix n n S) = g.map (algebraMap R S) := rfl

