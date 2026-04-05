import Mathlib

variable {R K : Type*} [CommRing R] [Field K]

theorem isParabolic_iff_of_upperTriangular_of_det [LinearOrder K] [IsStrictOrderedRing K]
    {g : GL (Fin 2) K} (h_det : g.det = 1 ∨ g.det = -1) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (∃ x ≠ 0, g = Matrix.GeneralLinearGroup.upperRightHom x) ∨ (∃ x ≠ 0, g = -Matrix.GeneralLinearGroup.upperRightHom x) := by
  rw [Matrix.GeneralLinearGroup.isParabolic_iff_of_upperTriangular hg10]
  constructor
  · rintro ⟨hg00, hg01⟩
    have : g 1 1 ^ 2 = 1 := by
      have : g.det = g 1 1 ^ 2 := by rw [val_det_apply, det_fin_two, hg10, hg00]; ring
      simp only [Units.ext_iff, Units.val_one, Units.val_neg, this] at h_det
      exact h_det.resolve_right (neg_one_lt_zero.trans_le <| sq_nonneg _).ne'
    apply (sq_eq_one_iff.mp this).imp <;> intro hg11 <;> simp only [Units.ext_iff]
    · refine ⟨g 0 1, hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
    · refine ⟨-g 0 1, neg_eq_zero.not.mpr hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;>
    simpa using hx

