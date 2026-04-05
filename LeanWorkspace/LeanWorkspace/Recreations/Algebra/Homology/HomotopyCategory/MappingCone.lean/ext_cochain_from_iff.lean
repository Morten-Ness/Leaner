import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem ext_cochain_from_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain (CochainComplex.mappingCone φ) K j} :
    γ₁ = γ₂ ↔
      (CochainComplex.mappingCone.inl φ).comp γ₁ (show _ = i by lia) = (CochainComplex.mappingCone.inl φ).comp γ₂ (by lia) ∧
        (Cochain.ofHom (CochainComplex.mappingCone.inr φ)).comp γ₁ (zero_add j) =
          (Cochain.ofHom (CochainComplex.mappingCone.inr φ)).comp γ₂ (zero_add j) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [CochainComplex.mappingCone.ext_from_iff φ (p + 1) p rfl]
    replace h₁ := Cochain.congr_v h₁ (p + 1) q (by lia)
    replace h₂ := Cochain.congr_v h₂ p q (by lia)
    simp only [Cochain.comp_v (CochainComplex.mappingCone.inl φ) _ _ (p + 1) p q (by lia) hpq] at h₁
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at h₂
    exact ⟨h₁, h₂⟩

