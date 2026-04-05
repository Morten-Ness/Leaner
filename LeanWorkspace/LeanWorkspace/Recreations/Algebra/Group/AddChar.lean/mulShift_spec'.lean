import Mathlib

variable {R M : Type*} [Ring R] [CommMonoid M]

theorem mulShift_spec' (ψ : AddChar R M) (n : ℕ) (x : R) : AddChar.mulShift ψ n x = ψ x ^ n := by
  rw [mulShift_apply, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

