import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem ext_component_iff {f g : ⨁ i, M i} :
    f = g ↔ ∀ i, DirectSum.component R ι M i f = DirectSum.component R ι M i g := by
  constructor
  · intro h i
    simp [h]
  · intro h
    ext i
    exact h i
