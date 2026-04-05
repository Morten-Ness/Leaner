import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem XIsoOfEq_inv_comp_d (K : HomologicalComplex V c) {p₂ p₁ : ι} (h : p₂ = p₁) (p₃ : ι) :
    (K.XIsoOfEq h).inv ≫ K.d p₂ p₃ = K.d p₁ p₃ := by subst h; simp

