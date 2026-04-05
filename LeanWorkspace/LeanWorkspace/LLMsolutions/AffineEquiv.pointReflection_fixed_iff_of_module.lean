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
    have h' := congrArg ((· -ᵥ x)) h
    simp [AffineEquiv.pointReflection_apply, vsub_vadd, two_smul, bit0, add_comm, add_left_comm,
      add_assoc] at h'
    rw [← sub_eq_zero] at h'
    have h2 : (2 : k) • (y -ᵥ x) = 0 := by
      simpa [two_smul, bit0] using h'
    have hhalf := congrArg ((⅟ (2 : k)) • ·) h2
    rw [smul_zero] at hhalf
    simpa [smul_smul, invOf_mul_self, one_smul] using hhalf
  · intro h
    subst h
    simp [AffineEquiv.pointReflection_apply]
