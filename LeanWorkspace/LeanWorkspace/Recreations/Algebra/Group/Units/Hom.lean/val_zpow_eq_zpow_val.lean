import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

variable {α : Type*} [DivisionMonoid α]

theorem val_zpow_eq_zpow_val : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = (u : α) ^ n := (Units.coeHom α).map_zpow

