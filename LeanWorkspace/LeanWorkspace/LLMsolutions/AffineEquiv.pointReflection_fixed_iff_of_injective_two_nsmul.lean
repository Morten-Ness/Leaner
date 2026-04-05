FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P₁}
    (h : Function.Injective (2 • · : V₁ → V₁)) : AffineEquiv.pointReflection k x y = y ↔ y = x := by
  constructor
  · intro hy
    have h0 : 2 • (x -ᵥ y) = 0 := by
      calc
        2 • (x -ᵥ y) = (AffineEquiv.pointReflection k x y -ᵥ y) := by
          rw [AffineEquiv.pointReflection_apply, two_nsmul, ← vsub_vadd, vadd_vsub_assoc]
        _ = y -ᵥ y := by rw [hy]
        _ = 0 := vsub_self y
    have hv : x -ᵥ y = (0 : V₁) := h h0
    have hxy : x = y := by
      rw [← vsub_eq_zero_iff_eq] at hv
      exact hv
    simpa [hxy] using hxy.symm
  · intro hy
    subst hy
    exact AffineEquiv.pointReflection_self k x
