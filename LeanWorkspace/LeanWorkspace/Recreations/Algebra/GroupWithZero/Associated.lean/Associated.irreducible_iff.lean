import Mathlib

variable {M : Type*}

theorem Associated.irreducible_iff [Monoid M] {p q : M} (h : p ~ᵤ q) :
    Irreducible p ↔ Irreducible q := ⟨h.irreducible, Associated.symm h.irreducible⟩

