import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_binomial' (k m : ℕ) (x y : R) :
    Polynomial.support (Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m) ⊆ {k, m} := Polynomial.support_add.trans
    (union_subset
      ((Polynomial.support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((Polynomial.support_C_mul_X_pow' m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

