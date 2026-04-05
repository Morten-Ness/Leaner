import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Abelian C]

variable {S : ShortComplex C}

theorem Exact.liftFromProjective_comp
    (hS : S.Exact) {P : C} (f : P ⟶ S.X₂) [Projective P] (hf : f ≫ S.g = 0) :
    hS.liftFromProjective f hf ≫ S.f = f := by
  dsimp [liftFromProjective]
  rw [← toCycles_i, Projective.factorThru_comp_assoc, liftCycles_i]

