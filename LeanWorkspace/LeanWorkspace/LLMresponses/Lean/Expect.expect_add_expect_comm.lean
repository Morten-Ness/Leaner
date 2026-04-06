FAIL
import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_add_expect_comm (f₁ f₂ g₁ g₂ : ι → M) :
    𝔼 i ∈ s, (f₁ i + f₂ i) + 𝔼 i ∈ s, (g₁ i + g₂ i) =
      𝔼 i ∈ s, (f₁ i + g₁ i) + 𝔼 i ∈ s, (f₂ i + g₂ i) := by
  simp_rw [Finset.expect_add_distrib]
  calc
    (𝔼 i ∈ s, f₁ i) + (𝔼 i ∈ s, f₂ i) + ((𝔼 i ∈ s, g₁ i) + (𝔼 i ∈ s, g₂ i))
        = (𝔼 i ∈ s, f₁ i) + ((𝔼 i ∈ s, f₂ i) + ((𝔼 i ∈ s, g₁ i) + (𝔼 i ∈ s, g₂ i))) := by
            rw [add_assoc]
    _ = (𝔼 i ∈ s, f₁ i) + ((𝔼 i ∈ s, g₁ i) + ((𝔼 i ∈ s, f₂ i) + (𝔼 i ∈ s, g₂ i))) := by
          congr 1
          rw [add_assoc, add_comm (𝔼 i ∈ s, f₂ i) (𝔼 i ∈ s, g₁ i), ← add_assoc]
    _ = (𝔼 i ∈ s, f₁ i) + (𝔼 i ∈ s, g₁ i) + ((𝔼 i ∈ s, f₂ i) + (𝔼 i ∈ s, g₂ i)) := by
          rw [← add_assoc]
    _ = (𝔼 i ∈ s, (f₁ i + g₁ i)) + (𝔼 i ∈ s, (f₂ i + g₂ i)) := by
          simp_rw [Finset.expect_add_distrib]
