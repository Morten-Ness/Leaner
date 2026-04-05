import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem Monic.mul_natDegree_lt_iff (h : Polynomial.Monic p) {q : R[X]} :
    (p * q).natDegree < p.natDegree ↔ p ≠ 1 ∧ q = 0 := by
  by_cases hq : q = 0
  · suffices 0 < p.natDegree ↔ p.natDegree ≠ 0 by simpa [hq, ← h.natDegree_eq_zero]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Nat.zero_le _) h.symm⟩
  · simp [h.natDegree_mul', hq]

