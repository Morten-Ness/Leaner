import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem sub_dvd_eval_sub (a b : R) (p : R[X]) : a - b ∣ p.eval a - p.eval b := by
  suffices Polynomial.X - Polynomial.C b ∣ p - Polynomial.C (p.eval b) by
    simpa only [coe_evalRingHom, eval_sub, eval_X, eval_C]
      using (_root_.map_dvd (evalRingHom a)) this
  simp [Polynomial.dvd_iff_isRoot]

