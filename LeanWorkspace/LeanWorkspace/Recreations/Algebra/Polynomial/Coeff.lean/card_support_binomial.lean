import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem card_support_binomial {k m : ℕ} (h : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    #(support (Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m)) = 2 := by
  rw [Polynomial.support_binomial h hx hy, card_insert_of_notMem (mt mem_singleton.mp h), card_singleton]

