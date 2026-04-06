FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem injective_pointReflection_left_of_module [Invertible (2 : k)] :
    ∀ y, Function.Injective fun x : P₁ => AffineEquiv.pointReflection k x y := by
  intro y x₁ x₂ h
  have h' := congrArg (fun p : P₁ => (x₁ -ᵥ p : V₁)) h
  simp only [AffineEquiv.pointReflection_apply, vsub_vadd, vsub_eq_sub] at h'
  simpa [two_nsmul, bit0, smul_add, add_comm, add_left_comm, add_assoc] using h'
