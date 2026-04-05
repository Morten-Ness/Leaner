import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]

variable [Algebra R S] {a : A} {f : S → R}

theorem map_zero (h : QuasispectrumRestricts a f) : f 0 = 0 := by
  rw [← h.left_inv 0, map_zero (algebraMap R S)]

