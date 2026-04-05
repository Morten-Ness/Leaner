import Mathlib

variable {k A G : Type*}

theorem AddMonoidAlgebra.mem_ideal_span_of'_image [AddMonoid A] [Semiring k] {s : Set A}
    {x : AddMonoidAlgebra k A} :
    x ∈ Ideal.span (AddMonoidAlgebra.of' k A '' s) ↔ ∀ m ∈ x.support, ∃ m' ∈ s, ∃ d, m = d + m' := @MonoidAlgebra.mem_ideal_span_of_image k (Multiplicative A) _ _ _ _

