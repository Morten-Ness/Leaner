import Mathlib

variable {R M M₁ : Type*} [AddCommMonoid M] [AddCommMonoid M₁]

theorem range_smulRight_apply_of_surjective [Semiring R] [Module R M] [Module R M₁]
    {f : M →ₗ[R] R} (hf : Function.Surjective f) (x : M₁) :
    range (f.smulRight x) = Submodule.span R {x} := Submodule.ext fun z ↦ by
  simp_rw [mem_range, smulRight_apply, Submodule.mem_span_singleton]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨f w, hw ▸ rfl⟩, fun ⟨w, hw⟩ ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hf w
  exact ⟨y, hw⟩

