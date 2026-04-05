import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem card_support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) : #(support (Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m + Polynomial.C z * Polynomial.X ^ n)) = 3 := by
  rw [Polynomial.support_trinomial hkm hmn hx hy hz,
    card_insert_of_notMem
      (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
    card_insert_of_notMem (mt mem_singleton.mp hmn.ne), card_singleton]

