import Mathlib

open scoped ComplexConjugate

variable {I : Type u}

variable {f : I → Type v}

theorem conj_apply {ι : Type*} {α : ι → Type*} [∀ i, CommSemiring (α i)] [∀ i, StarRing (α i)]
    (f : ∀ i, α i) (i : ι) : conj f i = conj (f i) := rfl

