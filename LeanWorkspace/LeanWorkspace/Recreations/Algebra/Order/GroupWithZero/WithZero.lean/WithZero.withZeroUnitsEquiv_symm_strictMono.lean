import Mathlib

variable {α : Type*} [LinearOrderedCommGroupWithZero α]

theorem WithZero.withZeroUnitsEquiv_symm_strictMono :
    StrictMono (withZeroUnitsEquiv (G := α)).symm :=
  OrderIso.withZeroUnits.symm.strictMono

