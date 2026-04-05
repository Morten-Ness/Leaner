import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem XIsoOfEq_inv_comp_XIsoOfEq_hom (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₂₁ : p₂ = p₁) (h₂₃ : p₂ = p₃) :
    (K.XIsoOfEq h₂₁).inv ≫ (K.XIsoOfEq h₂₃).hom = (K.XIsoOfEq (h₂₁.symm.trans h₂₃)).hom := by
  dsimp [HomologicalComplex.XIsoOfEq]
  simp only [eqToHom_trans]

