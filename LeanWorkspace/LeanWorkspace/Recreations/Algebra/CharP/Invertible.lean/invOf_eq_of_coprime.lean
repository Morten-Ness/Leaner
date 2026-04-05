import Mathlib

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem invOf_eq_of_coprime {n : ℕ} [Invertible (n : R)] (h : n.Coprime p) :
    ⅟(n : R) = n.gcdA p := by
  letI : Invertible (n : R) := invertibleOfCoprime h
  convert (rfl : ⅟(n : R) = _)

