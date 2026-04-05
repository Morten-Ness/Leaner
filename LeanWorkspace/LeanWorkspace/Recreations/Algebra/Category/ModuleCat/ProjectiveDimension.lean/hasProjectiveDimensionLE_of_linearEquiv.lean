import Mathlib

variable {R : Type u} [CommRing R] [Small.{v} R]

variable [Small.{v'} R] {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R}

theorem hasProjectiveDimensionLE_of_linearEquiv (e : M ≃ₗ[R] N)
    (n : ℕ) [HasProjectiveDimensionLE M n] : HasProjectiveDimensionLE N n := CategoryTheory.hasProjectiveDimensionLE_of_semiLinearEquiv (RingEquiv.refl R) e n

