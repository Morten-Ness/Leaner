import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem map_mapGL {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (g : Matrix.SpecialLinearGroup n R) :
    (Matrix.SpecialLinearGroup.mapGL S g).map (algebraMap S T) = Matrix.SpecialLinearGroup.mapGL T g := by
  ext
  simp [IsScalarTower.algebraMap_apply R S T]

