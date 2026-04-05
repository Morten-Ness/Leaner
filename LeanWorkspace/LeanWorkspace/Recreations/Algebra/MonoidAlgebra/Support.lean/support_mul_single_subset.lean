import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

variable [Mul G]

theorem support_mul_single_subset [DecidableEq G] (f : k[G]) (r : k) (a : G) :
    (f * single a r).support ⊆ Finset.image (· * a) f.support := (MonoidAlgebra.support_mul _ _).trans <| (Finset.image₂_subset_left support_single_subset).trans <| by
    rw [Finset.image₂_singleton_right]

