import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem mem_span (x : M) : x ∈ span R (Set.range b) := span_mono (image_subset_range _ _) (Module.Basis.mem_span_repr_support b x)

