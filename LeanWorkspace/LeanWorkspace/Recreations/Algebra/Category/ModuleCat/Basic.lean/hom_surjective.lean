import Mathlib

variable (R : Type u) [Ring R]

theorem hom_surjective {M N : ModuleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) := ModuleCat.hom_bijective.surjective

