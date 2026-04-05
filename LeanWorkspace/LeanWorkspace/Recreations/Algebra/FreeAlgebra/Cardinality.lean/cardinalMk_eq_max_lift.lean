import Mathlib

variable (R : Type u) [CommSemiring R]

variable (X : Type v)

theorem cardinalMk_eq_max_lift [Nonempty X] [Nontrivial R] :
    #(FreeAlgebra R X) = Cardinal.lift.{v} #R ⊔ Cardinal.lift.{u} #X ⊔ ℵ₀ := by
  have hX := mk_freeMonoid X
  rw [equivMonoidAlgebraFreeMonoid.toEquiv.cardinal_eq, MonoidAlgebra,
    mk_finsupp_lift_of_infinite, hX, lift_max, lift_aleph0, sup_comm, ← sup_assoc]

