import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem singleton_add_eq (a : A) (r : R) : {r} + σ a = σ (↑ₐ r + a) := ext fun x => by
    rw [singleton_add, image_add_left, mem_preimage, add_comm, spectrum.add_mem_iff, map_neg, neg_neg]

