import Mathlib

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem pointwise_vadd_eq_map (v : V) (s : AffineSubspace k P) :
    v +ᵥ s = s.map (AffineEquiv.constVAdd k P v) := rfl

