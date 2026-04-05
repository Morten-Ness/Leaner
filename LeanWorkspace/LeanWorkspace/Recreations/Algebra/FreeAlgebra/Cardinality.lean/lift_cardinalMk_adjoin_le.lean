import Mathlib

variable (R : Type u) [CommSemiring R]

theorem lift_cardinalMk_adjoin_le {A : Type v} [Semiring A] [Algebra R A] (s : Set A) :
    lift.{u} #(adjoin R s) ≤ lift.{v} #R ⊔ lift.{u} #s ⊔ ℵ₀ := by
  have H := mk_range_le_lift (f := FreeAlgebra.lift R ((↑) : s → A))
  rw [lift_umax, lift_id'.{v, u}] at H
  rw [Algebra.adjoin_eq_range_freeAlgebra_lift]
  exact H.trans (FreeAlgebra.cardinalMk_le_max_lift R s)

