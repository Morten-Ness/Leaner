import Mathlib

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

variable (φ ψ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_sub : HomologicalComplex.homologyMap (φ - ψ) i = HomologicalComplex.homologyMap φ i - HomologicalComplex.homologyMap ψ i := by
  dsimp [HomologicalComplex.homologyMap]
  rw [← ShortComplex.homologyMap_sub]
  rfl

