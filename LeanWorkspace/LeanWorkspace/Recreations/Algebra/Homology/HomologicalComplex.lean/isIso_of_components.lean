import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem isIso_of_components (f : C₁ ⟶ C₂) [∀ n : ι, IsIso (f.f n)] : IsIso f := (HomologicalComplex.Hom.isoOfComponents fun n => asIso (f.f n)).isIso_hom

