import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [CompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

theorem sSup_mul : sSup (s * t) = sSup s * sSup t := (sSup_image2_eq_sSup_sSup fun _ => (OrderIso.mulRight _).to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).to_galoisConnection

