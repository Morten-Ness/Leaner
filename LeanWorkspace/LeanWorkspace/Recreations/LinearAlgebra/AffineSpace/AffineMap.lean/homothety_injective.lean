import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
    (hr : r ≠ 0) :
    Function.Injective (AffineMap.homothety c r) := fun _ _ h ↦ by simpa [AffineMap.homothety_def, hr] using h

