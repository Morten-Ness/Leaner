import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_def (c : P1) (r : k) :
    AffineMap.homothety c r = r • (id k P1 -ᵥ AffineMap.const k P1 c) +ᵥ AffineMap.const k P1 c := rfl

