import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_modByMonic_le_left : degree (p %ₘ q) ≤ degree p := by
  nontriviality R
  by_cases hq : q.Monic
  · cases lt_or_ge (degree p) (degree q)
    · rw [(Polynomial.modByMonic_eq_self_iff hq).mpr ‹_›]
    · exact (Polynomial.degree_modByMonic_le p hq).trans ‹_›
  · rw [Polynomial.modByMonic_eq_of_not_monic p hq]

