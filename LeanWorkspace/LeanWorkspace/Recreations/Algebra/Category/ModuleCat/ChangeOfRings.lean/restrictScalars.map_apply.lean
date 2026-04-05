import Mathlib

theorem restrictScalars.map_apply {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M M' : ModuleCat.{v} S} (g : M ⟶ M') (x) : (ModuleCat.restrictScalars f).map g x = g x := rfl

