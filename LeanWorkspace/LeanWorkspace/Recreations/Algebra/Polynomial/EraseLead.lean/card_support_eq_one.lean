import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eq_one : #f.support = 1 ↔
    ∃ (k : ℕ) (x : R) (_ : x ≠ 0), f = Polynomial.C x * Polynomial.X ^ k := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, _, hx, rfl⟩ := Polynomial.card_support_eq.mp h
    exact ⟨k 0, x 0, hx 0, Fin.sum_univ_one _⟩
  · rintro ⟨k, x, hx, rfl⟩
    rw [support_C_mul_X_pow k hx, card_singleton]

