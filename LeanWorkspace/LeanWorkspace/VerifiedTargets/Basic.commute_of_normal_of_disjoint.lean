import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem commute_of_normal_of_disjoint (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
    (hdis : Disjoint H₁ H₂) (x y : G) (hx : x ∈ H₁) (hy : y ∈ H₂) : Commute x y := by
  suffices x * y * x⁻¹ * y⁻¹ = 1 by
    change x * y = y * x
    · rw [mul_assoc, mul_eq_one_iff_eq_inv] at this
      simpa
  apply hdis.le_bot
  constructor
  · suffices x * (y * x⁻¹ * y⁻¹) ∈ H₁ by simpa [mul_assoc]
    exact H₁.mul_mem hx (hH₁.conj_mem _ (H₁.inv_mem hx) _)
  · change x * y * x⁻¹ * y⁻¹ ∈ H₂
    apply H₂.mul_mem _ (H₂.inv_mem hy)
    apply hH₂.conj_mem _ hy

