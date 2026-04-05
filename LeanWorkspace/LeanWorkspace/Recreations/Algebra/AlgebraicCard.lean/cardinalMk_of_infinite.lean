import Mathlib

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_of_infinite [Infinite R] : #{ x : A // IsAlgebraic R x } = #R := lift_inj.1 <| Algebraic.cardinalMk_lift_of_infinite R A

