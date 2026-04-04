import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_add (c : P1) (r₁ r₂ : k) :
    AffineMap.homothety c (r₁ + r₂) = r₁ • (id k P1 -ᵥ AffineMap.const k P1 c) +ᵥ AffineMap.homothety c r₂ := by
  simp only [AffineMap.homothety_def, add_smul, vadd_vadd]

