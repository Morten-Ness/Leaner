import Mathlib

variable {M : Type*} {N : Type*}

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

theorem coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1 := (Subtype.ext_iff.symm : (x : M₁) = (1 : S') ↔ x = 1)

