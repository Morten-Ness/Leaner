import Mathlib

variable {R S : Type*} [Semiring R] [SetLike S R] [hSR : NonUnitalSubsemiringClass S R] (s : S)

theorem unitization_apply (x : Unitization ℕ s) : NonUnitalSubsemiring.unitization s x = x.fst + x.snd := rfl

