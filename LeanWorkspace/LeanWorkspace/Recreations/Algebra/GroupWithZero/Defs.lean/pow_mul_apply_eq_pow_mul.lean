import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MonoidWithZero M₀]

theorem pow_mul_apply_eq_pow_mul {M : Type*} [Monoid M] (f : M₀ → M) {x : M₀}
    (hx : ∀ y : M₀, f (x * y) = f x * f y) (n : ℕ) :
    ∀ (y : M₀), f (x ^ n * y) = f x ^ n * f y := by
  induction n with
  | zero => intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n hn => intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

