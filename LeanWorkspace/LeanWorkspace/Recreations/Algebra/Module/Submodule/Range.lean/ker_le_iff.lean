import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable [Ring R] [Ring R₂]

variable [AddCommGroup M] [AddCommGroup M₂]

variable [Module R M] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂}

variable {f : M →ₛₗ[τ₁₂] M₂}

theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} :
    ker f ≤ p ↔ ∃ y ∈ LinearMap.range f, f ⁻¹' {y} ⊆ p := by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe, LinearMap.coe_range]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker] at hz
    rw [← SetLike.mem_coe, LinearMap.coe_range, Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x ∈ p := h₂ hx
    have hxz : z + x ∈ p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x ∈ p by simpa only [this, add_sub_cancel_right]
    exact p.sub_mem hxz hx'

