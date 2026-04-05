import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem X_dvd_iff {f : R[X]} : Polynomial.X ∣ f ↔ f.coeff 0 = 0 := ⟨fun ⟨g, hfg⟩ => by rw [hfg, coeff_X_mul_zero], fun hf =>
    ⟨f.divX, by rw [← add_zero (Polynomial.X * f.divX), ← C_0, ← hf, X_mul_divX_add]⟩⟩

