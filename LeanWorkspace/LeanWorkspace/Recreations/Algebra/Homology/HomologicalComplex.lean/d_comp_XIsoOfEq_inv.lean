import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem d_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₂ p₃ : ι} (h : p₃ = p₂) (p₁ : ι) :
    K.d p₁ p₂ ≫ (K.XIsoOfEq h).inv = K.d p₁ p₃ := by subst h; simp

