import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_surjective {M N : SemimoduleCat.{v} R} :
    Function.Surjective (Hom.hom : (M ⟶ N) → (M →ₗ[R] N)) := SemimoduleCat.hom_bijective.surjective

