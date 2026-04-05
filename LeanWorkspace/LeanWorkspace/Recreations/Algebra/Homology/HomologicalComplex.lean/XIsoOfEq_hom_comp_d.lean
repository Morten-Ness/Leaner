import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem XIsoOfEq_hom_comp_d (K : HomologicalComplex V c) {p₁ p₂ : ι} (h : p₁ = p₂) (p₃ : ι) :
    (K.XIsoOfEq h).hom ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

