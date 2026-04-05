import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R]

variable [Semiring S] {f : R →+* S}

theorem _root_.Function.Injective.monic_map_iff (hf : Function.Injective f) {p : R[X]} :
    p.Monic ↔ (p.map f).Monic := ⟨Polynomial.Monic.map _, Polynomial.monic_of_injective hf⟩

