import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem prev_eq (f : HomologicalComplex.Hom C₁ C₂) {i j : ι} (w : c.Rel i j) :
    ChainComplex.prev f j = (C₁.xPrevIso w).hom ≫ f.f i ≫ (C₂.xPrevIso w).inv := by
  obtain rfl := c.prev_eq' w
  simp only [HomologicalComplex.xPrevIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

