import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_support (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
    (Polynomial.trinomial k m n u v w).support = {k, m, n} := support_trinomial hkm hmn hu hv hw

