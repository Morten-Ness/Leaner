import Mathlib

variable {α β γ : Type*}

variable {M G : Type*}

variable [AddGroup G]

theorem log_inv : ∀ x : Gᵐ⁰, WithZero.log x⁻¹ = -WithZero.log x
  | 0 => by simp
  | (x : Multiplicative G) => rfl
