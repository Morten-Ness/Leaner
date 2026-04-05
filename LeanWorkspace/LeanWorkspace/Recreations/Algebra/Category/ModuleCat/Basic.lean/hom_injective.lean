import Mathlib

variable (R : Type u) [Ring R]

theorem hom_injective {M N : ModuleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) := ModuleCat.hom_bijective.injective

