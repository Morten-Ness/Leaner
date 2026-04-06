FAIL
import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem div_apply' (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a / χ a := by
  change ((ψ * χ⁻¹) : AddChar A M) a = ψ a / χ a
  simp
