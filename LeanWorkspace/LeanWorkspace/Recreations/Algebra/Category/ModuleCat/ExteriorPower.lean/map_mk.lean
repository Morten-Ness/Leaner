import Mathlib

variable {R : Type u} [CommRing R]

theorem map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : ℕ} (x : Fin n → M) :
    ModuleCat.exteriorPower.map f n (ModuleCat.exteriorPower.mk x) = ModuleCat.exteriorPower.mk (f ∘ x) := by
  apply ModuleCat.exteriorPower.map_apply_ιMulti

