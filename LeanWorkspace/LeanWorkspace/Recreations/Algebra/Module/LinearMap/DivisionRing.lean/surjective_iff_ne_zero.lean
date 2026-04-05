import Mathlib

variable {R M M₁ : Type*} [AddCommMonoid M] [AddCommMonoid M₁]

theorem surjective_iff_ne_zero [DivisionSemiring R] [Module R M] {f : M →ₗ[R] R} :
    Function.Surjective f ↔ f ≠ 0 := by
  refine ⟨ne_zero_of_surjective, fun hf z ↦ ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by simpa [Ne, LinearMap.ext_iff] using hf
  exact ⟨(z * (f y)⁻¹) • y, by simp [hy]⟩

protected alias ⟨_, surjective⟩ := surjective_iff_ne_zero

