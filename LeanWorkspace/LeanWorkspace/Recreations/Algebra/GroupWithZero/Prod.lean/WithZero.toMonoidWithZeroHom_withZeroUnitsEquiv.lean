import Mathlib

variable {M₀ N₀ : Type*}

theorem WithZero.toMonoidWithZeroHom_withZeroUnitsEquiv [GroupWithZero M₀]
    [DecidablePred fun x : M₀ ↦ x = 0] :
    MonoidWithZeroHomClass.toMonoidWithZeroHom WithZero.withZeroUnitsEquiv =
      WithZero.lift' (Units.coeHom M₀) := rfl

