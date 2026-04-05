import Mathlib

variable (R : Type*) [Ring R] {S : Type*} [AddCommGroup S] [Pow S ℕ] [Module R S] (p q : R[X])
  (x : S)

theorem smeval_neg_nat (S : Type*) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] (q : ℕ[X])
    (n : ℕ) : q.smeval (-(n : S)) = q.smeval (-n : ℤ) := by
  rw [Polynomial.smeval_eq_sum, Polynomial.smeval_eq_sum]
  simp only [Polynomial.smul_pow, sum_def]
  simp

