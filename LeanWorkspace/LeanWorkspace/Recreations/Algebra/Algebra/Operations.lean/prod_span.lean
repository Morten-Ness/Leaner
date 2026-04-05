import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem prod_span {ι : Type*} (s : Finset ι) (M : ι → Set A) :
    (∏ i ∈ s, Submodule.span R (M i)) = Submodule.span R (∏ i ∈ s, M i) := by
  letI := Classical.decEq ι
  refine Finset.induction_on s ?_ ?_
  · simp [Submodule.one_eq_span, Set.singleton_one]
  · intro _ _ H ih
    rw [Finset.prod_insert H, Finset.prod_insert H, ih, Submodule.span_mul_span]

