import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem contract_add {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    Polynomial.contract p (f + g) = Polynomial.contract p f + Polynomial.contract p g := by
  ext; simp_rw [coeff_add, Polynomial.coeff_contract hp, coeff_add]

