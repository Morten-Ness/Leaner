import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_inj [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r ≠ 0)
    {p q : P1} :
    AffineMap.homothety c r p = AffineMap.homothety c r q ↔ p = q := (AffineMap.homothety_injective c hr).eq_iff

