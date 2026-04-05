import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem IsUnit.of_pow_eq_one (ha : a ^ n = 1) (hn : n ≠ 0) : IsUnit a := (Units.ofPowEqOne _ n ha hn).isUnit

