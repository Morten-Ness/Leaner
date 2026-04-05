import Mathlib

theorem restrictScalars.smul_def' {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)
    {M : ModuleCat.{v} S} (r : R) (m : M) :
    r • (show (ModuleCat.restrictScalars f).obj M from m) = f r • m := rfl

