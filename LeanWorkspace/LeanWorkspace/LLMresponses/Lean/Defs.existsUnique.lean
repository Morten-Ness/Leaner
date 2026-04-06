import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem existsUnique : ∃! p, CharP R p := by
  refine ⟨ringChar R, ringChar.charP R, ?_⟩
  intro q hq
  exact CharP.eq R hq (ringChar.charP R)
