FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_mul (c : P1) (r₁ r₂ : k) :
    AffineMap.homothety c (r₁ * r₂) = (AffineMap.homothety c r₁).comp (AffineMap.homothety c r₂) := by
  ext p
  rw [AffineMap.comp_apply, AffineMap.homothety_apply, AffineMap.homothety_apply,
    AffineMap.homothety_apply, smul_smul]
