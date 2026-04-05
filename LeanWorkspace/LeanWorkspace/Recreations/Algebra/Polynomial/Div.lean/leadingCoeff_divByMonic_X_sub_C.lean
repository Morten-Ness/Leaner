import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

variable [IsDomain R]

theorem leadingCoeff_divByMonic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (Polynomial.X - Polynomial.C a)) = leadingCoeff p := by
  nontriviality
  rcases hp.lt_or_gt with hd | hd
  · rw [degree_eq_bot.mp <| Nat.WithBot.lt_zero_iff.mp hd, Polynomial.zero_divByMonic]
  refine Polynomial.leadingCoeff_divByMonic_of_monic (Polynomial.monic_X_sub_C a) ?_
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]

