import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_mul_apply (c : P1) (r₁ r₂ : k) (p : P1) :
    AffineMap.homothety c (r₁ * r₂) p = AffineMap.homothety c r₁ (AffineMap.homothety c r₂ p) := by
  simp only [AffineMap.homothety_apply, mul_smul, vadd_vsub]

