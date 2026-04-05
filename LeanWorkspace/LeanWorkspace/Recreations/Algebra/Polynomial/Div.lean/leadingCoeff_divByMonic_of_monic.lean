import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem leadingCoeff_divByMonic_of_monic (hmonic : q.Monic)
    (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff := by
  nontriviality
  have h : q.leadingCoeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [Polynomial.divByMonic_eq_zero_iff hmonic, hmonic.leadingCoeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw 2 [← Polynomial.modByMonic_add_div p q]
  rw [Polynomial.leadingCoeff_add_of_degree_lt, leadingCoeff_monic_mul hmonic]
  rw [degree_mul' h, Polynomial.degree_add_divByMonic hmonic hdegree]
  exact (Polynomial.degree_modByMonic_lt p hmonic).trans_le hdegree

