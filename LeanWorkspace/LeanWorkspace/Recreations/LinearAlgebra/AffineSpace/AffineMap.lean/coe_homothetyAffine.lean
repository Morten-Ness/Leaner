import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem coe_homothetyAffine (c : P1) : ⇑(AffineMap.homothetyAffine c : k →ᵃ[k] _) = AffineMap.homothety c := rfl

