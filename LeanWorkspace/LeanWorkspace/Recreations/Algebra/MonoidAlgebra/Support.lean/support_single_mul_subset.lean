import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

variable [Mul G]

theorem support_single_mul_subset [DecidableEq G] (f : k[G]) (r : k) (a : G) :
    (single a r * f : k[G]).support ⊆ Finset.image (a * ·) f.support := (MonoidAlgebra.support_mul _ _).trans <| (Finset.image₂_subset_right support_single_subset).trans <| by
    rw [Finset.image₂_singleton_left]

