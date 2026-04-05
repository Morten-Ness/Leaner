import Mathlib

variable (R : Type u) [CommSemiring R]

theorem cardinalMk_adjoin_le {A : Type u} [Semiring A] [Algebra R A] (s : Set A) :
    #(adjoin R s) ≤ #R ⊔ #s ⊔ ℵ₀ := by
  simpa using Algebra.lift_cardinalMk_adjoin_le R s

