import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eq_three :
    #f.support = 3 ↔
      ∃ (k m n : ℕ) (_ : k < m) (_ : m < n) (x y z : R) (_ : x ≠ 0) (_ : y ≠ 0) (_ : z ≠ 0),
        f = Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m + Polynomial.C z * Polynomial.X ^ n := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := Polynomial.card_support_eq.mp h
    refine
      ⟨k 0, k 1, k 2, hk Nat.zero_lt_one, hk (Nat.lt_succ_self 1), x 0, x 1, x 2, hx 0, hx 1, hx 2,
        ?_⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩
    exact card_support_trinomial hkm hmn hx hy hz

