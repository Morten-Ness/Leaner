import Mathlib

theorem restrictScalars.smul_def {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : (ModuleCat.restrictScalars f).obj M) : r • m = f r • show M from m := rfl

