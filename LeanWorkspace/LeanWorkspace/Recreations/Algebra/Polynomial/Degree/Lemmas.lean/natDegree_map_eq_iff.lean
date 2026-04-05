import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem natDegree_map_eq_iff {f : R →+* S} {p : Polynomial R} :
    natDegree (map f p) = natDegree p ↔ f (p.leadingCoeff) ≠ 0 ∨ natDegree p = 0 := by
  rcases eq_or_ne (natDegree p) 0 with h | h
  · simp_rw [h, ne_eq, or_true, iff_true, ← Nat.le_zero, ← h, natDegree_map_le]
  simp_all [natDegree, WithBot.unbotD_eq_unbotD_iff]

