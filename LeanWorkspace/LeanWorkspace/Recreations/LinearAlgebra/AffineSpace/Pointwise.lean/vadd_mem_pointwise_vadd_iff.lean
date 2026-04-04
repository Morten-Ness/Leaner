import Mathlib

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem vadd_mem_pointwise_vadd_iff {v : V} {s : AffineSubspace k P} {p : P} :
    v +ᵥ p ∈ v +ᵥ s ↔ p ∈ s := vadd_mem_vadd_set_iff

