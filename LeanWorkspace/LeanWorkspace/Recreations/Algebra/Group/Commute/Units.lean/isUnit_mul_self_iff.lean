import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem isUnit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a := (Commute.refl a).isUnit_mul_iff.trans and_self_iff

