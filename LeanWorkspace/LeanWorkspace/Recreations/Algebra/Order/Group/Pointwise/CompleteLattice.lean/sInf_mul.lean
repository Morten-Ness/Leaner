import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [CompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

theorem sInf_mul : sInf (s * t) = sInf s * sInf t := (sInf_image2_eq_sInf_sInf fun _ => (OrderIso.mulRight _).symm.to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galoisConnection

