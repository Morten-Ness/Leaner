import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem ext_component {f g : ⨁ i, M i} (h : ∀ i, DirectSum.component R ι M i f = DirectSum.component R ι M i g) :
    f = g := DFinsupp.ext h

