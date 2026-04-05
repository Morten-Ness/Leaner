import Mathlib

variable {𝕜 G : Type*}

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [Module 𝕜 G] {a : 𝕜} {b₁ b₂ : G}

variable [PosSMulMono 𝕜 G]

theorem smul_inv_le_iff_of_neg (h : a < 0) : b₁ ≤ a⁻¹ • b₂ ↔ b₂ ≤ a • b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

