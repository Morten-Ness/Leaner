import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem Units.pow_ofPowEqOne (ha : a ^ n = 1) (hn : n ≠ 0) :
    Units.ofPowEqOne _ n ha hn ^ n = 1 := Units.ext <| by simp [ha]

