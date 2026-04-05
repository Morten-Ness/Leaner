import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem irreducible_mul_isUnit (h : IsUnit x) : Irreducible (y * x) ↔ Irreducible y := let ⟨x, hx⟩ := h
  hx ▸ irreducible_mul_units x

