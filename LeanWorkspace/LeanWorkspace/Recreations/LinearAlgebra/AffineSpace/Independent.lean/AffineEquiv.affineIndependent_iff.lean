import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem AffineEquiv.affineIndependent_iff {p : ι → P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (e ∘ p) ↔ AffineIndependent k p := e.toAffineMap.affineIndependent_iff e.toEquiv.injective

set_option backward.isDefEq.respectTransparency false in

