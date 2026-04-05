import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem divX_eq_zero_iff : Polynomial.divX p = 0 ↔ p = Polynomial.C (p.coeff 0) := ⟨fun h => by simpa [eq_comm, h] using Polynomial.divX_mul_X_add p, fun h => by rw [h, Polynomial.divX_C]⟩

