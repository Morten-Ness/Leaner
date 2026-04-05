import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [SetLike S R] [hSR : SubringClass S R] (s : S)

theorem coe_natCast (n : ℕ) : ((n : s) : R) = n := rfl

