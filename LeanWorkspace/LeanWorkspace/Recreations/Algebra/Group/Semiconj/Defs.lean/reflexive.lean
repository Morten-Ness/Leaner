import Mathlib

variable {S M G : Type*}

variable [MulOneClass M]

theorem reflexive : Reflexive fun a b : M ↦ ∃ c, SemiconjBy c a b
  | a => ⟨1, SemiconjBy.one_left a⟩
