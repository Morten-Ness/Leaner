import Mathlib

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

variable [Countable R]

theorem cardinalMk_of_countable_of_charZero [CharZero A] :
    #{ x : A // IsAlgebraic R x } = ℵ₀ := (Algebraic.countable R A).le_aleph0.antisymm (Algebraic.aleph0_le_cardinalMk_of_charZero R A)

