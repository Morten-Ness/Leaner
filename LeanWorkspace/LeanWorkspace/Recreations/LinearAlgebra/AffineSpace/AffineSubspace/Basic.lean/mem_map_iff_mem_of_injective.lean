import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem mem_map_iff_mem_of_injective {f : P₁ →ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₁}
    (hf : Function.Injective f) : f x ∈ s.map f ↔ x ∈ s := hf.mem_set_image

