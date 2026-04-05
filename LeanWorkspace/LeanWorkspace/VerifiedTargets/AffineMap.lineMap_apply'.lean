import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

theorem lineMap_apply' [SMulCommClass k k V2] (f g : P1 →ᵃ[k] P2) (c : k)
    (p : P1) : AffineMap.lineMap f g c p = AffineMap.lineMap (f p) (g p) c := by
  simp [AffineMap.lineMap_apply]

