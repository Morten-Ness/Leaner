import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

theorem apply_lineMap (f : P1 →ᵃ[k] P2) (p₀ p₁ : P1) (c : k) :
    f (AffineMap.lineMap p₀ p₁ c) = AffineMap.lineMap (f p₀) (f p₁) c := by
  simp [AffineMap.lineMap_apply]
