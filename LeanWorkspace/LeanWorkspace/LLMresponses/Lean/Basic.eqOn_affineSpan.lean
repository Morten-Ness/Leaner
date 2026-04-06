FAIL
import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem eqOn_affineSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f g (affineSpan k s) := by
  let t : AffineSubspace k P₁ :=
    { carrier := {x | f x = g x}
      smul_vsub_vadd_mem := by
        intro p1 hp1 c p2 hp2
        change f (c • (p1 -ᵥ p2) +ᵥ p2) = g (c • (p1 -ᵥ p2) +ᵥ p2)
        rw [map_smul_vsub_vadd, map_smul_vsub_vadd, hp1, hp2] }
  have hs : s ⊆ (t : Set P₁) := h_agree
  have hspan : affineSpan k s ≤ t := affineSpan_le.2 hs
  exact hspan hx
