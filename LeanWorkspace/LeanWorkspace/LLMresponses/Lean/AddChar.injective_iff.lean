FAIL
import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem injective_iff {ψ : AddChar A M} : Function.Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 := by
  constructor
  · intro h x hx
    exact h <| by simpa using hx
  · intro h x y hxy
    have h0 : ψ (x - y) = 1 := by
      rw [show x - y = x + (-y) by abel]
      rw [AddChar.map_add]
      rw [hxy]
      exact div_self (ψ y)
    have hsub : x - y = 0 := h h0
    exact sub_eq_zero.mp hsub
