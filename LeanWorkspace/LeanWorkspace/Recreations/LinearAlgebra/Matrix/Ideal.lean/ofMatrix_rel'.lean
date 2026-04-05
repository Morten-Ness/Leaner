import Mathlib

variable {R n : Type*}

variable [NonAssocSemiring R] [Fintype n]

theorem ofMatrix_rel' [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} (i j : n) :
    RingCon.ofMatrix c x y ↔ c (single i j x) (single i j y) := by
  refine ⟨fun h ↦ h i j, fun h i' j' ↦ ?_⟩
  simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

