FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem injective_pointReflection_left_of_injective_two_nsmul
    (h : Function.Injective (2 • · : V₁ → V₁)) (y : P₁) :
    Function.Injective fun x : P₁ => AffineEquiv.pointReflection k x y := by
  intro x₁ x₂ hxe
  let z : P₁ := AffineEquiv.pointReflection k x₁ y
  have hz1 : z = AffineEquiv.pointReflection k x₁ y := rfl
  have hz2 : z = AffineEquiv.pointReflection k x₂ y := by simpa [z] using hxe
  have hv1 : (x₁ -ᵥ z) = (z -ᵥ y) := by
    rw [hz1, AffineEquiv.pointReflection_apply]
  have hv2 : (x₂ -ᵥ z) = (z -ᵥ y) := by
    rw [hz2, AffineEquiv.pointReflection_apply]
  have hv : x₁ -ᵥ z = x₂ -ᵥ z := hv1.trans hv2.symm
  exact vsub_right_cancel hv
