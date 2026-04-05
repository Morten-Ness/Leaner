import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem XIsoOfEq_hom_comp_XIsoOfEq_inv (K : HomologicalComplex V c) {p₁ p₂ p₃ : ι}
    (h₁₂ : p₁ = p₂) (h₃₂ : p₃ = p₂) :
    (K.XIsoOfEq h₁₂).hom ≫ (K.XIsoOfEq h₃₂).inv = (K.XIsoOfEq (h₁₂.trans h₃₂.symm)).hom := by
  dsimp [HomologicalComplex.XIsoOfEq]
  simp only [eqToHom_trans]

