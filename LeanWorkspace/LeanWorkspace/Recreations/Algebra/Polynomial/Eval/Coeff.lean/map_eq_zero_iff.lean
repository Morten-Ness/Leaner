import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_eq_zero_iff (hf : Function.Injective f) : p.map f = 0 ↔ p = 0 := map_eq_zero_iff (mapRingHom f) (Polynomial.map_injective f hf)

