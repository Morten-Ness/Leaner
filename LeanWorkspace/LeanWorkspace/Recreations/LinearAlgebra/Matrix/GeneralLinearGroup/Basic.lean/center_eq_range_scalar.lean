import Mathlib

variable {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem center_eq_range_scalar :
    Subgroup.center (GL n R) = (scalar n).range := by
  ext g
  constructor
  · -- previous lemma shows the underlying matrix is scalar, but now need to show
    -- the scalar is a unit; so we apply argument both to `g` and `g⁻¹`
    intro hg
    cases isEmpty_or_nonempty n with
    | inl hn => simp [nontriviality]
    | inr hn =>
      obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hg
      obtain ⟨b, hb⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp (Subgroup.inv_mem _ hg)
      have hab : a * b = 1 := by
        simpa [-mul_inv_cancel, ← ha, ← hb, ← diagonal_one, Units.ext_iff] using mul_inv_cancel g
      refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, ?_⟩
      simp [Units.ext_iff, ← ha]
  · rintro ⟨a, rfl⟩
    exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, rfl⟩

