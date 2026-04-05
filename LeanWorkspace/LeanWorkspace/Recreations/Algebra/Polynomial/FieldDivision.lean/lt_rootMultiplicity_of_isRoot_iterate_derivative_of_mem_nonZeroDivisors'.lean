import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t)
    (hnzd : ∀ m ≤ n, m ≠ 0 → (m : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  apply Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors h hroot
  clear hroot
  induction n with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one]
    exact Submonoid.one_mem _
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, mul_mem_nonZeroDivisors]
    exact ⟨hnzd _ le_rfl n.succ_ne_zero, ih fun m h ↦ hnzd m (h.trans n.le_succ)⟩

