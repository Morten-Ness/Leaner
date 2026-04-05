import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem dvd_iff_isRoot : Polynomial.X - Polynomial.C a ∣ p ↔ IsRoot p a := ⟨fun h => by
    rwa [← Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C _), Polynomial.modByMonic_X_sub_C_eq_C_eval, ← C_0,
      C_inj] at h,
    fun h => ⟨p /ₘ (Polynomial.X - Polynomial.C a), by rw [Polynomial.mul_divByMonic_eq_iff_isRoot.2 h]⟩⟩

