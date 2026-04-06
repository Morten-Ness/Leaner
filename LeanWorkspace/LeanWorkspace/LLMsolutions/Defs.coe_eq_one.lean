import Mathlib

variable {M : Type*} {N : Type*}

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 := by
  constructor
  · intro hx
    apply Subtype.ext
    simpa using hx
  · intro hx
    simpa using congrArg (fun y : S' => (y : M₁)) hx
