FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem vadd_lineMap (v : V₁) (p₁ p₂ : P₁) (c : k) :
    v +ᵥ AffineMap.lineMap p₁ p₂ c = AffineMap.lineMap (v +ᵥ p₁) (v +ᵥ p₂) c := by
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
  rw [vadd_vsub_assoc, vadd_vsub_assoc]
  simp [smul_vsub_vadd, add_comm, add_left_comm, add_assoc]
