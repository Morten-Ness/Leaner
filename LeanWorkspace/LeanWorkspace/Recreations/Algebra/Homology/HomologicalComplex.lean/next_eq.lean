import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem next_eq (f : HomologicalComplex.Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    ChainComplex.next f i = (C₁.xNextIso w).hom ≫ f.f j ≫ (C₂.xNextIso w).inv := by
  obtain rfl := c.next_eq' w
  simp only [HomologicalComplex.xNextIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

