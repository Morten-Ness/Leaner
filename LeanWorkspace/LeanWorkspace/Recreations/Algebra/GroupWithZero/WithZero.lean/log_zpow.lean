import Mathlib

variable {α β γ : Type*}

variable {M G : Type*}

variable [AddGroup G]

theorem log_zpow (x : Gᵐ⁰) (n : ℤ) : WithZero.log (x ^ n) = n • WithZero.log x := by cases n <;> simp [WithZero.log_pow, WithZero.log_inv]

