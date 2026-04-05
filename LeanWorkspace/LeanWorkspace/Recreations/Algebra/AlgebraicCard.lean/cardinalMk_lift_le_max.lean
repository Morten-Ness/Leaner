import Mathlib

variable (R : Type u) (A : Type v) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Module.IsTorsionFree R A]

theorem cardinalMk_lift_le_max :
    Cardinal.lift.{u} #{ x : A // IsAlgebraic R x } ≤ max (Cardinal.lift.{v} #R) ℵ₀ := (Algebraic.cardinalMk_lift_le_mul R A).trans <| by grw [lift_le.2 cardinalMk_le_max]; simp

