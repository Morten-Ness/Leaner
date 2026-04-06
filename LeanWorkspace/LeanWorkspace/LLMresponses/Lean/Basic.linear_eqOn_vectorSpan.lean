FAIL
import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem linear_eqOn_vectorSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f.linear g.linear (vectorSpan k s) := by
  classical
  by_cases hs : s.Nonempty
  · rcases hs with ⟨p₀, hp₀⟩
    have hlin :
        ∀ p ∈ s, f.linear (p -ᵥ p₀) = g.linear (p -ᵥ p₀) := by
      intro p hp
      rw [AffineMap.linear_apply]
      rw [AffineMap.linear_apply]
      rw [h_agree hp, h_agree hp₀]
    intro v hv
    rw [vectorSpan_eq_span_vsub_set_right_ne k hs] at hv
    refine Submodule.span_induction hv hlin ?_ ?_ ?_
    · simpa using hp₀
    · simp
    · intro x y hx hy
      simp [hx, hy]
    · intro a x hx
      simp [hx]
  · have hs' : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    intro v hv
    rw [vectorSpan_empty] at hv
    exact hv.elim
