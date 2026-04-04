import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem map_comap_le (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f).map f ≤ s := (AffineSubspace.gc_map_comap f).l_u_le _

