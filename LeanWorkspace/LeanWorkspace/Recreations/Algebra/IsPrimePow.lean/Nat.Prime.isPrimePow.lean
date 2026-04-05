import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem Nat.Prime.isPrimePow {p : ℕ} (hp : p.Prime) : IsPrimePow p := Prime.isPrimePow _root_ (prime_iff.mp hp)

