import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem contravariant_le_of_contravariant_eq_and_lt [PartialOrder N]
    [ContravariantClass M N μ (· = ·)] [ContravariantClass M N μ (· < ·)] :
    ContravariantClass M N μ (· ≤ ·) where
  elim := (contravariant_le_iff_contravariant_lt_and_eq M N μ).mpr
    ⟨ContravariantClass.elim, ContravariantClass.elim⟩

