import Mathlib

open scoped Polynomial

variable {R S : Type*}

variable [Semiring R]

theorem _root_.Polynomial.toLaurent_inj (f g : R[X]) : toLaurent f = toLaurent g ↔ f = g := ⟨fun h => Polynomial.toLaurent_injective h, congr_arg _⟩

