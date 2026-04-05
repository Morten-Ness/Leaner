import Mathlib

variable {R : Type*}

variable [Semiring R] {p q : SkewPolynomial R}

variable {S S₁ S₂ : Type*}

variable [MulSemiringAction (Multiplicative ℕ) R]

theorem φ_iterate_apply (n : ℕ) (a : R) : (φ^[n] a) = ((ofAdd n) • a) := by
  induction n with
  | zero => simp
  | succ n hn =>
    simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

