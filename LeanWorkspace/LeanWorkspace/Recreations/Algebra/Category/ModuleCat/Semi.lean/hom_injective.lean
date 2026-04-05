import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_injective {M N : SemimoduleCat.{v} R} :
    Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) := SemimoduleCat.hom_bijective.injective

