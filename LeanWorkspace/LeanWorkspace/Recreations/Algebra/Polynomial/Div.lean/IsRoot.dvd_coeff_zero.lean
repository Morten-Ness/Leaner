import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem IsRoot.dvd_coeff_zero {p : R[X]} {x : R} (h : p.IsRoot x) : x ∣ p.coeff 0 := by
  simpa [h.eq_zero, coeff_zero_eq_eval_zero] using Polynomial.sub_dvd_eval_sub 0 x p

