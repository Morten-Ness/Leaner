import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S S₁ S₂ : ShortComplex C}

variable (h : S.LeftHomologyData) (F : C ⥤ D)

variable [F.PreservesZeroMorphisms]

variable [h.IsPreservedBy F]

set_option backward.isDefEq.respectTransparency false in
theorem map_f' : (h.map F).f' = F.map h.f' := by
  rw [← cancel_mono (h.map F).i, f'_i, map_f, map_i, ← F.map_comp, f'_i]

