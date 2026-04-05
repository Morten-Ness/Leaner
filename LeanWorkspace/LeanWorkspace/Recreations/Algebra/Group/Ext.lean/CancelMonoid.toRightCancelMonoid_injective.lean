import Mathlib

theorem CancelMonoid.toRightCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toRightCancelMonoid M) := by
  intro m₁ m₂ h
  apply CancelMonoid.ext
  exact congrArg (fun m : Monoid M => (letI := m; HMul.hMul : M → M → M)) <|
    congrArg (@RightCancelMonoid.toMonoid M) h

