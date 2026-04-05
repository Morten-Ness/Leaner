import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem XIsoOfEq_hom_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₁₂.trans h₂₃)).hom := by
  dsimp [HomologicalComplex.XIsoOfEq]
  simp only [eqToHom_trans]

