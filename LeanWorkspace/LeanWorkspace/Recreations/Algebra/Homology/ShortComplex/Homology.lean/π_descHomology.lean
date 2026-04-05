import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem π_descHomology (k : S.cycles ⟶ A) (hk : S.toCycles ≫ k = 0) :
    S.homologyπ ≫ S.descHomology k hk = k := Cofork.IsColimit.π_desc S.homologyIsCokernel

