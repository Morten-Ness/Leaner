import Mathlib

variable {A B : CommRingCat.{u}} {f : A ⟶ B}
  {M : ModuleCat.{u} B} (D : M.Derivation f)

set_option backward.isDefEq.respectTransparency false in
theorem desc_d (b : B) : CommRingCat.KaehlerDifferential.D.desc (CommRingCat.KaehlerDifferential.d b) = CommRingCat.KaehlerDifferential.D.d b := by
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  apply CommRingCat.KaehlerDifferential.D.liftKaehlerDifferential_comp_D

