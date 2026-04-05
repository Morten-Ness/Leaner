import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable [K.HasHomology i]

variable [L.HasHomology i] [M.HasHomology i]

set_option backward.isDefEq.respectTransparency false in
theorem cyclesMap_comp : HomologicalComplex.cyclesMap (φ ≫ ψ) i = HomologicalComplex.cyclesMap φ i ≫ HomologicalComplex.cyclesMap ψ i := by
  dsimp [HomologicalComplex.cyclesMap]
  rw [Functor.map_comp, ShortComplex.cyclesMap_comp]

