import Mathlib

variable {M k V P V₁ P₁ V₂ P₂ : Type*}

variable [Ring k]

variable [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem pointwise_vadd_span (v : V) (s : Set P) : v +ᵥ affineSpan k s = affineSpan k (v +ᵥ s) := map_span _ s

