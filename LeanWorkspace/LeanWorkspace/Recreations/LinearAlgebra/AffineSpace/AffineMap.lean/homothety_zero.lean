import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_zero (c : P1) : AffineMap.homothety c (0 : k) = AffineMap.const k P1 c := by
  ext p
  simp [AffineMap.homothety_apply]

