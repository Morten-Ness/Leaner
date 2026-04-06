FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem commute_of_normal_of_disjoint (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
    (hdis : Disjoint H₁ H₂) (x y : G) (hx : x ∈ H₁) (hy : y ∈ H₂) : Commute x y := by
  rw [commute_iff_eq]
  have hcomm_mem_H₁ : x * y * x⁻¹ * y⁻¹ ∈ H₁ := by
    have h1 : x * y * x⁻¹ ∈ H₁ := hH₁.conj_mem x hy
    exact H₁.mul_mem h1 (H₁.inv_mem hx)
  have hcomm_mem_H₂ : x * y * x⁻¹ * y⁻¹ ∈ H₂ := by
    have h1 : y * x * y⁻¹ ∈ H₂ := hH₂.conj_mem y hx
    have h1' : x * y * x⁻¹ * y⁻¹ = x * (y * x * y⁻¹) * x⁻¹ := by
      simp [mul_assoc]
    rw [h1']
    exact hH₂.conj_mem x h1
  have hcomm_eq_one : x * y * x⁻¹ * y⁻¹ = 1 := by
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ H₁ ⊓ H₂ := ⟨hcomm_mem_H₁, hcomm_mem_H₂⟩
    have hbot : H₁ ⊓ H₂ = ⊥ := disjoint_iff.mp hdis
    have hmem' : x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by simpa [hbot] using hmem
    simpa using hmem'
  have h1 : x * y * x⁻¹ = y := by
    have := congrArg (fun z => z * y) hcomm_eq_one
    simpa [mul_assoc] using this
  have h2 : x * y = y * x := by
    have := congrArg (fun z => z * x) h1
    simpa [mul_assoc] using this
  exact h2
