import Mathlib

variable (R : Type u) [Ring R]

theorem hom_id {M : ModuleCat.{v} R} : (𝟙 M : M ⟶ M).hom = LinearMap.id := rfl

