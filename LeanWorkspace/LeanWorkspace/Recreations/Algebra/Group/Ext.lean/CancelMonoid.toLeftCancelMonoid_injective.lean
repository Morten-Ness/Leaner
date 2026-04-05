import Mathlib

theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) := by
  rintro ⟨⟩ ⟨⟩ h
  congr

