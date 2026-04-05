import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem RightHomologyData.exact_map_iff (h : S.RightHomologyData) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h.IsPreservedBy F] [(S.map F).HasHomology] :
    (S.map F).Exact ↔ IsZero (F.obj h.H) := (h.map F).exact_iff

