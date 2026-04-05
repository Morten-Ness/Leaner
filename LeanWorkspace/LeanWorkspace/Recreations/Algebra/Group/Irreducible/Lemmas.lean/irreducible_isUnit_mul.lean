import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem irreducible_isUnit_mul (h : IsUnit x) : Irreducible (x * y) ↔ Irreducible y := let ⟨x, ha⟩ := h
  ha ▸ irreducible_units_mul x

