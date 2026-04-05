import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

theorem degree_comp [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hq : 0 < q.degree) :
    (p.comp q).degree = p.degree * q.degree := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp, degree_zero, WithBot.bot_mul']
    simp [hq.ne']
  rw [degree_eq_natDegree hp, degree_eq_natDegree (ne_zero_of_degree_gt hq), ← Nat.cast_mul,
    ← Polynomial.natDegree_comp]
  apply degree_eq_natDegree
  simp_rw [Ne, Polynomial.comp_eq_zero_iff, hp, false_or, not_and_or, ← degree_le_zero_iff]
  simp [hq]

