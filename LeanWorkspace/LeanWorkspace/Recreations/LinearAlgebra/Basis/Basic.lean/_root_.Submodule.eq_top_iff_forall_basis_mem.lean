import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem _root_.Submodule.eq_top_iff_forall_basis_mem {p : Submodule R M} :
    p = ⊤ ↔ ∀ i, b i ∈ p := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  replace h : Set.range b ⊆ p := by rintro - ⟨i, rfl⟩; exact h i
  simpa using span_mono (R := R) h

