import Mathlib

variable {R K : Type*}

variable [Ring R] {p : ℕ} [CharP R p]

theorem CharP.natCast_gcdA_mul_intCast_eq_gcd (n : ℕ) :
    (n.gcdA p * n : R) = n.gcd p := Nat.commute_cast _ _ |>.eq.trans <| CharP.intCast_mul_natCast_gcdA_eq_gcd n

