import Mathlib

variable {R n : Type*}

variable [NonUnitalNonAssocSemiring R] [Fintype n]

theorem ofMatrix_rel [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} :
    RingCon.ofMatrix c x y ↔ ∀ i j, c (single i j x) (single i j y) := Iff.rfl

