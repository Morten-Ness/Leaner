import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem IsNilpotent.pow_succ (n : ℕ) {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (x ^ n.succ) := have ⟨N, hN⟩ := hx
  ⟨N, by rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]⟩

