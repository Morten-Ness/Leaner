import Mathlib

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.isUnit_ofNat_iff {n : ℕ} [n.AtLeastTwo] (hp : p.Prime) :
    IsUnit (ofNat(n) : R) ↔ ¬p ∣ ofNat(n) := CharP.isUnit_natCast_iff hp

