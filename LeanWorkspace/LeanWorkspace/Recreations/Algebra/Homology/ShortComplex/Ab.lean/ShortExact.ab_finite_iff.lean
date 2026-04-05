import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ShortExact.ab_finite_iff {S : CategoryTheory.ShortComplex Ab.{u}} (hS : S.ShortExact) :
    Finite S.X₂ ↔ Finite S.X₁ ∧ Finite S.X₃ where
  mp _ := ⟨.of_injective _ hS.ab_injective_f, .of_surjective _ hS.ab_surjective_g⟩
  mpr | ⟨_, _⟩ => hS.exact.ab_finite

