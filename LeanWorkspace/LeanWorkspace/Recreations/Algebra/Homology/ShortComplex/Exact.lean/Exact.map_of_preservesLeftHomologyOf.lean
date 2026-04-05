import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem Exact.map_of_preservesLeftHomologyOf (h : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [(S.map F).HasHomology] : (S.map F).Exact := by
  have := h.hasHomology
  rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero] at h
  rw [S.leftHomologyData.exact_map_iff F, IsZero.iff_id_eq_zero,
    ← F.map_id, h, F.map_zero]

