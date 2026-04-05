import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem exact_map_iff_of_faithful [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] [F.Faithful] :
    (S.map F).Exact ↔ S.Exact := by
  constructor
  · intro h
    rw [S.leftHomologyData.exact_iff, IsZero.iff_id_eq_zero]
    rw [(S.leftHomologyData.map F).exact_iff, IsZero.iff_id_eq_zero,
      LeftHomologyData.map_H] at h
    apply F.map_injective
    rw [F.map_id, F.map_zero, h]
  · intro h
    exact h.map F

