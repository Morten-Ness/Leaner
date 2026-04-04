import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

variable {P1}

variable {k}

variable (k) in

theorem right_vsub_lineMap (p₀ p₁ : P1) (c : k) : p₁ -ᵥ AffineMap.lineMap p₀ p₁ c = (1 - c) • (p₁ -ᵥ p₀) := by
  rw [← AffineMap.lineMap_apply_one_sub, AffineMap.left_vsub_lineMap]

