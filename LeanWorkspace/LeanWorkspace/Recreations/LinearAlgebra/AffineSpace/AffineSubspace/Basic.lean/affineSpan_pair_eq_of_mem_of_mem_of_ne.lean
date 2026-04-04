import Mathlib

variable {k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem affineSpan_pair_eq_of_mem_of_mem_of_ne {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ line[k, p₃, p₄])
    (hp₂ : p₂ ∈ line[k, p₃, p₄]) (hp₁₂ : p₁ ≠ p₂) : line[k, p₁, p₂] = line[k, p₃, p₄] := by
  refine le_antisymm (affineSpan_pair_le_of_mem_of_mem hp₁ hp₂) ?_
  rw [← vsub_vadd p₁ p₃, vadd_left_mem_affineSpan_pair] at hp₁
  rcases hp₁ with ⟨r₁, hp₁⟩
  rw [← vsub_vadd p₂ p₃, vadd_left_mem_affineSpan_pair] at hp₂
  rcases hp₂ with ⟨r₂, hp₂⟩
  have hr₀ : r₂ - r₁ ≠ 0 := by
    rw [sub_ne_zero]
    rintro rfl
    simp_all
  have hr : (r₂ - r₁) • (p₄ -ᵥ p₃) = p₂ -ᵥ p₁ := by
    simp [sub_smul, hp₁, hp₂]
  rw [← eq_inv_smul_iff₀ hr₀] at hr
  refine affineSpan_pair_le_of_mem_of_mem ?_ ?_
  · convert smul_vsub_vadd_mem_affineSpan_pair (-r₁ * (r₂ - r₁)⁻¹) p₁ p₂
    simp [mul_smul, ← hr, hp₁]
  · convert smul_vsub_vadd_mem_affineSpan_pair ((1 - r₁) * (r₂ - r₁)⁻¹) p₁ p₂
    simp [mul_smul, ← hr, sub_smul, hp₁]

