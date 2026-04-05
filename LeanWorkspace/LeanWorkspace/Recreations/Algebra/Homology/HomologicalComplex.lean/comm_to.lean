import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem comm_to (f : HomologicalComplex.Hom C₁ C₂) (j : ι) : ChainComplex.prev f j ≫ C₂.dTo j = C₁.dTo j ≫ f.f j := f.comm _ _

attribute [simp] comm_to_apply

