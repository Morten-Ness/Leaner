import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem isGLB_sInf (S : Set (Subfield K)) : IsGLB S (sInf S) := by
  have : ∀ {s t : Subfield K}, (s : Set K) ≤ t ↔ s ≤ t := by simp [SetLike.coe_subset_coe]
  refine IsGLB.of_image this ?_
  convert isGLB_biInf (s := S) (f := SetLike.coe)
  exact Subfield.coe_sInf _

