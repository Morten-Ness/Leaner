import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem inv_pow' (A : M) (n : ℕ) : A⁻¹ ^ n = (A ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ A, mul_inv_rev, ← ih, ← pow_succ']

