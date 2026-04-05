FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem lineMap_vsub (p₁ p₂ p₃ : P₁) (c : k) :
    AffineMap.lineMap p₁ p₂ c -ᵥ p₃ = AffineMap.lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₃) c := by
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
  simp [AffineMap.lineMap_apply, lineMap_apply_module, sub_eq_add_neg, add_comm, add_left_comm,
    add_assoc, smul_add, add_smul]
