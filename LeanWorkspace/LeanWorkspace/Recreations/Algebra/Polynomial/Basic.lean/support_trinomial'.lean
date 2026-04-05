import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_trinomial' (k m n : ℕ) (x y z : R) :
    Polynomial.support (Polynomial.C x * Polynomial.X ^ k + Polynomial.C y * Polynomial.X ^ m + Polynomial.C z * Polynomial.X ^ n) ⊆ {k, m, n} := Polynomial.support_add.trans
    (union_subset
      (Polynomial.support_add.trans
        (union_subset
          ((Polynomial.support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((Polynomial.support_C_mul_X_pow' m y).trans
            (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
      ((Polynomial.support_C_mul_X_pow' n z).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

