FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem vsub_lineMap (p₁ p₂ p₃ : P₁) (c : k) :
    p₁ -ᵥ AffineMap.lineMap p₂ p₃ c = AffineMap.lineMap (p₁ -ᵥ p₂) (p₁ -ᵥ p₃) c := by
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
  rw [vsub_add_vsub_cancel, ← add_vsub_assoc, ← add_vsub_assoc]
  abel_nf
