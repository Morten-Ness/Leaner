import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem map_sup (s t : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) : (s ⊔ t).map f = s.map f ⊔ t.map f := (AffineSubspace.gc_map_comap f).l_sup

