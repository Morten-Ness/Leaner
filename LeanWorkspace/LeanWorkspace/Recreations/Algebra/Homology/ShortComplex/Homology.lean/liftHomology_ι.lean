import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem liftHomology_ι (k : A ⟶ S.opcycles) (hk : k ≫ S.fromOpcycles = 0) :
    S.liftHomology k hk ≫ S.homologyι = k := Fork.IsLimit.lift_ι S.homologyIsKernel

