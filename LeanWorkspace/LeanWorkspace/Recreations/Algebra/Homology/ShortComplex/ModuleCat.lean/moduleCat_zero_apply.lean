import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 := S.zero_apply x

