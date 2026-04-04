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

theorem lineMap_vsub_lineMap (p₁ p₂ p₃ p₄ : P1) (c : k) :
    AffineMap.lineMap p₁ p₂ c -ᵥ AffineMap.lineMap p₃ p₄ c = AffineMap.lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) c := ((AffineMap.fst : P1 × P1 →ᵃ[k] P1) -ᵥ (AffineMap.snd : P1 × P1 →ᵃ[k] P1)).apply_lineMap (_, _) (_, _) c

