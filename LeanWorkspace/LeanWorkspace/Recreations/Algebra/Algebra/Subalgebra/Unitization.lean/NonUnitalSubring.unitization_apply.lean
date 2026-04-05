import Mathlib

variable {R S : Type*} [Ring R] [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

theorem unitization_apply (x : Unitization ℤ s) : NonUnitalSubring.unitization s x = x.fst + x.snd := rfl

