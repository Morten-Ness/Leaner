import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eq_two :
    #f.support = 2 ↔
      ∃ (k m : ℕ) (_ : k < m) (x y : R) (_ : x ≠ 0) (_ : y ≠ 0),
        f = Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := Polynomial.card_support_eq.mp h
    refine ⟨k 0, k 1, hk Nat.zero_lt_one, x 0, x 1, hx 0, hx 1, ?_⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    exact card_support_binomial hkm.ne hx hy

