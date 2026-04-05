import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem prod_span_singleton {ι : Type*} (s : Finset ι) (x : ι → A) :
    (∏ i ∈ s, span R ({x i} : Set A)) = span R {∏ i ∈ s, x i} := by
  rw [Submodule.prod_span, Set.finset_prod_singleton]

