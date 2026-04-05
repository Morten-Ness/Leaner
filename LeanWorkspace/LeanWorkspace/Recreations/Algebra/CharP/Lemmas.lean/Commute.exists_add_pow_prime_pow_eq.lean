import Mathlib

variable {R S : Type*}

variable [Semiring R] {p : ℕ} (hp : p.Prime) {x y : R}

theorem exists_add_pow_prime_pow_eq (h : Commute x y) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r := ⟨_, h.add_pow_prime_pow_eq hp n⟩

