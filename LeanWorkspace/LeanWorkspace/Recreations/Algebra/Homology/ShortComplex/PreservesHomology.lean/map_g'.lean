import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S S₁ S₂ : ShortComplex C}

variable (h : S.RightHomologyData) (F : C ⥤ D)

variable [F.PreservesZeroMorphisms]

variable [h.IsPreservedBy F]

set_option backward.isDefEq.respectTransparency false in
theorem map_g' : (h.map F).g' = F.map h.g' := by
  rw [← cancel_epi (h.map F).p, p_g', map_g, map_p, ← F.map_comp, p_g']

