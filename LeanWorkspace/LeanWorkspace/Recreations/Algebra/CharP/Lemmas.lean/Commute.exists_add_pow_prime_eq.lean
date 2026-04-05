import Mathlib

variable {R S : Type*}

variable [Semiring R] {p : ℕ} (hp : p.Prime) {x y : R}

theorem exists_add_pow_prime_eq (h : Commute x y) :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r := ⟨_, h.add_pow_prime_eq hp⟩

