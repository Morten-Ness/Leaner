import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Abelian C]

variable {S : ShortComplex C}

theorem Exact.comp_descToInjective
    (hS : S.Exact) {J : C} (f : S.X₂ ⟶ J) [Function.Injective J] (hf : S.f ≫ f = 0) :
    S.g ≫ hS.descToInjective f hf = f := by
  dsimp [descToInjective]
  simp only [← p_fromOpcycles, assoc, Function.Injective.comp_factorThru, p_descOpcycles]

