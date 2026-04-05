import Mathlib

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.intCast_mul_natCast_gcdA_eq_gcd (n : ℕ) :
    (n * n.gcdA p : R) = n.gcd p := by
  suffices ↑(n * n.gcdA p + p * n.gcdB p : ℤ) = ((n.gcd p : ℤ) : R) by simpa using this
  rw [← Nat.gcd_eq_gcd_ab]

