import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem mem_span_repr_support (m : M) : m ∈ span R (b '' (b.repr m).support) := (Finsupp.mem_span_image_iff_linearCombination _).2
    ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩

