import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] (k m n : ℕ) (u v w : R)

theorem trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hw : w ≠ 0) :
    (Polynomial.trinomial k m n u v w).mirror = Polynomial.trinomial k (n - m + k) n w v u := by
  rw [mirror, Polynomial.trinomial_natTrailingDegree hkm hmn hu, reverse, Polynomial.trinomial_natDegree hkm hmn hw,
    Polynomial.trinomial_def, reflect_add, reflect_add, reflect_C_mul_X_pow, reflect_C_mul_X_pow,
    reflect_C_mul_X_pow, revAt_le (hkm.trans hmn).le, revAt_le hmn.le, revAt_le le_rfl, add_mul,
    add_mul, mul_assoc, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add,
    Nat.sub_add_cancel (hkm.trans hmn).le, Nat.sub_self, zero_add, add_comm, add_comm (C u * X ^ n),
    ← add_assoc, ← Polynomial.trinomial_def]

