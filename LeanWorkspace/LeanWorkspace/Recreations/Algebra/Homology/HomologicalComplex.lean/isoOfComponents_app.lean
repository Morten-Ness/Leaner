import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem isoOfComponents_app (f : ∀ i, C₁.X i ≅ C₂.X i)
    (hf : ∀ i j, c.Rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) (i : ι) :
    HomologicalComplex.Hom.isoApp (HomologicalComplex.Hom.isoOfComponents f hf) i = f i := by
  ext
  simp

