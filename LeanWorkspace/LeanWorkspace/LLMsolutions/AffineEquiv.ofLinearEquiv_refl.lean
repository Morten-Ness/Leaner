import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

variable {k V P : Type*}

variable [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem ofLinearEquiv_refl (p : P) :
    AffineEquiv.ofLinearEquiv (.refl k V) p p = .refl k P := by
  ext q <;> simp [AffineEquiv.ofLinearEquiv]
