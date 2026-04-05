import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem comap_supr {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₂) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (AffineSubspace.gc_map_comap f).u_iInf

