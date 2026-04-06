FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem pointReflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} :
    AffineEquiv.pointReflection k x y = y ↔ y = x := by
  constructor
  · intro h
    have h' := congrArg ((· -ᵥ y) : P₁ → V₁) h
    rw [AffineEquiv.pointReflection_apply, vsub_vadd, vsub_eq_sub] at h'
    have h2 : (2 : k) • (x -ᵥ y) = 0 := by
      simpa [two_nsmul] using h'
    have h3 : x -ᵥ y = 0 := by
      let hInv : k := ⅟ (2 : k)
      have := congrArg ((hInv • ·) : V₁ → V₁) h2
      simpa [smul_smul] using this
    exact (vsub_eq_zero_iff_eq.mp h3).symm
  · intro h
    subst h
    simp
