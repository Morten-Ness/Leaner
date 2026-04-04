import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem ext_on {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} (h_span : affineSpan k s = ⊤)
    (T₁ T₂ : P₁ ≃ᵃ[k] P₂) (h_agree : s.EqOn T₁ T₂) : T₁ = T₂ := AffineEquiv.toAffineMap_inj.mp <| AffineMap.ext_on h_span h_agree

