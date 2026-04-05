import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem contract_expand {f : R[X]} (hp : p ≠ 0) : Polynomial.contract p (Polynomial.expand R p f) = f := by
  ext
  simp [Polynomial.coeff_contract hp, Polynomial.coeff_expand hp.bot_lt, Nat.mul_div_cancel _ hp.bot_lt]

