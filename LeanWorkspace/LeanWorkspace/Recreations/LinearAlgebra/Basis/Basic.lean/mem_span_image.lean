import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem mem_span_image {m : M} {s : Set ι} : m ∈ span R (b '' s) ↔ ↑(b.repr m).support ⊆ s := ⟨Module.Basis.repr_support_subset_of_mem_span _ _, fun h ↦
    span_mono (Set.image_mono h) (Module.Basis.mem_span_repr_support b _)⟩

