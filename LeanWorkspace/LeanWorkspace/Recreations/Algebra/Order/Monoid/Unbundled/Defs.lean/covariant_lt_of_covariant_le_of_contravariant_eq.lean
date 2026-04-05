import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem covariant_lt_of_covariant_le_of_contravariant_eq [ContravariantClass M N μ (· = ·)]
    [PartialOrder N] [CovariantClass M N μ (· ≤ ·)] : CovariantClass M N μ (· < ·) where
  elim a _ _ bc := (CovariantClass.elim a bc.le).lt_of_ne (bc.ne ∘ ContravariantClass.elim _)

