import Mathlib

variable (R : Type u) [CommSemiring R]

variable (X : Type v)

theorem cardinalMk_eq_lift [IsEmpty X] : #(FreeAlgebra R X) = Cardinal.lift.{v} #R := by
  have := lift_mk_eq'.2 ⟨show (FreeMonoid X →₀ R) ≃ R from Equiv.finsuppUnique⟩
  rw [lift_id'.{u, v}, lift_umax] at this
  rwa [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, MonoidAlgebra]

