import Mathlib

variable {R M : Type*}

theorem isTorsion_iff_isTorsion_int [AddCommGroup M] :
    AddMonoid.IsTorsion M ↔ Module.IsTorsion ℤ M := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, h0, hn⟩ := (h x).exists_nsmul_eq_zero
    exact
      ⟨⟨n, mem_nonZeroDivisors_of_ne_zero <| ne_of_gt <| Int.natCast_pos.mpr h0⟩,
        (natCast_zsmul _ _).trans hn⟩
  · rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    exact ⟨_, Int.natAbs_pos.2 (nonZeroDivisors.coe_ne_zero n), natAbs_nsmul_eq_zero.2 hn⟩

