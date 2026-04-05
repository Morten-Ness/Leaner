FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem injective_pointReflection_left_of_injective_two_nsmul
    (h : Function.Injective (2 • · : V₁ → V₁)) (y : P₁) :
    Function.Injective fun x : P₁ => AffineEquiv.pointReflection k x y := by
  intro x₁ x₂ hxy
  apply h
  have h' := congrArg (fun z : P₁ => z -ᵥ y) hxy
  simpa [AffineEquiv.pointReflection_apply, two_nsmul] using h'
