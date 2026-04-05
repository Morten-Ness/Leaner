import Mathlib

variable {R : Type u} [CommRing R] [Small.{v} R]

variable [Small.{v'} R] {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}

theorem projectiveDimension_eq_of_linearEquiv (e : M ≃ₗ[R] N) :
    projectiveDimension M = projectiveDimension N := CategoryTheory.projectiveDimension_eq_of_semiLinearEquiv (M := M) (N := N) (RingEquiv.refl R) e

