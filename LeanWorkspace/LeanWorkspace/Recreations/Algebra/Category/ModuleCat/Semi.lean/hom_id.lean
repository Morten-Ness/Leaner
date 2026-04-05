import Mathlib

variable (R : Type u) [Semiring R]

theorem hom_id {M : SemimoduleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

