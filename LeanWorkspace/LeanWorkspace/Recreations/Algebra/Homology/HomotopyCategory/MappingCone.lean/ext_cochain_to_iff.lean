import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem ext_cochain_to_iff (i j : ℤ) (hij : i + 1 = j)
    {K : CochainComplex C ℤ} {γ₁ γ₂ : Cochain K (CochainComplex.mappingCone φ) i} :
    γ₁ = γ₂ ↔ γ₁.comp (CochainComplex.mappingCone.fst φ).1 hij = γ₂.comp (CochainComplex.mappingCone.fst φ).1 hij ∧
      γ₁.comp (CochainComplex.mappingCone.snd φ) (add_zero i) = γ₂.comp (CochainComplex.mappingCone.snd φ) (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    ext p q hpq
    rw [CochainComplex.mappingCone.ext_to_iff φ q (q + 1) rfl]
    replace h₁ := Cochain.congr_v h₁ p (q + 1) (by lia)
    replace h₂ := Cochain.congr_v h₂ p q hpq
    simp only [Cochain.comp_v _ _ _ p q (q + 1) hpq rfl] at h₁
    simp only [Cochain.comp_zero_cochain_v] at h₂
    exact ⟨h₁, h₂⟩

