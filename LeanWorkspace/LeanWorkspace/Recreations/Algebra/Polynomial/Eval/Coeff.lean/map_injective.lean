import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := fun p q h =>
  ext fun m => hf <| by rw [← Polynomial.coeff_map f, ← Polynomial.coeff_map f, h]

