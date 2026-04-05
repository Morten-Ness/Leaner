import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem XIsoOfEq_inv_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₃₂.trans h₂₁).symm).hom := by
  dsimp [HomologicalComplex.XIsoOfEq]
  simp only [eqToHom_trans]

