import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem inv_pow (a : α) : ∀ n : ℕ, a⁻¹ ^ n = (a ^ n)⁻¹
  | 0 => by rw [pow_zero, pow_zero, inv_one]
  | n + 1 => by rw [pow_succ', pow_succ, inv_pow _ n, mul_inv_rev]

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
