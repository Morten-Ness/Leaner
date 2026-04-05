import Mathlib

variable {A B : CommRingCat.{u}} (M : ModuleCat.{v} B) (f : A ⟶ B)

variable (D : M.Derivation f)

theorem d_map (a : A) : D.d (f a) = 0 := letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  D.map_algebraMap a

