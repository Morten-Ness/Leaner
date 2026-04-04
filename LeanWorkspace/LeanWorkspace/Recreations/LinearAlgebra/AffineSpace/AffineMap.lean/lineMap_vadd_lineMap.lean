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

theorem lineMap_vadd_lineMap (v₁ v₂ : V1) (p₁ p₂ : P1) (c : k) :
    AffineMap.lineMap v₁ v₂ c +ᵥ AffineMap.lineMap p₁ p₂ c = AffineMap.lineMap (v₁ +ᵥ p₁) (v₂ +ᵥ p₂) c := ((AffineMap.fst : V1 × P1 →ᵃ[k] V1) +ᵥ (AffineMap.snd : V1 × P1 →ᵃ[k] P1)).apply_lineMap (v₁, p₁) (v₂, p₂) c

