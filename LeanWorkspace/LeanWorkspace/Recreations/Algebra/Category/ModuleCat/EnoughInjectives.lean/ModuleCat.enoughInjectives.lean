import Mathlib

variable (R : Type u) [Ring R]

theorem ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R) := EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap ℤ R))

