FAIL
import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem injective_iff {ψ : AddChar A M} : Function.Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 := by
  constructor
  · intro h x hx
    apply h
    simpa [map_zero] using hx
  · intro h x y hxy
    have h1 : ψ (x - y) = 1 := by
      rw [map_sub, hxy, div_self]
    have hs : x - y = 0 := h h1
    exact sub_eq_zero.mp hs
