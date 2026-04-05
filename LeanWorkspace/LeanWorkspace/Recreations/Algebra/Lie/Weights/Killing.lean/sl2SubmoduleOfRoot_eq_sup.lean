import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

variable [IsKilling K L]

variable [IsTriangularizable K H L]

variable [CharZero K]

theorem sl2SubmoduleOfRoot_eq_sup (α : Weight K H L) (hα : α.IsNonZero) :
    LieAlgebra.IsKilling.sl2SubmoduleOfRoot hα = genWeightSpace L α ⊔ genWeightSpace L (-α) ⊔ corootSubmodule α := by
  ext x
  obtain ⟨h', e, f, ht, heα, hfα⟩ := LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero hα
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · replace hx : x ∈ LieAlgebra.IsKilling.sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    refine add_mem (add_mem ?_ ?_) ?_
    · exact mem_sup_left <| mem_sup_left <| smul_mem _ _ heα
    · exact mem_sup_left <| mem_sup_right <| smul_mem _ _ hfα
    · suffices ∃ y ∈ corootSpace α, H.subtype y = c₃ • h' from
        mem_sup_right <| by simpa [ht.lie_e_f, -Subtype.exists]
      refine ⟨c₃ • LieAlgebra.IsKilling.coroot α, smul_mem _ _ <| by simp, ?_⟩
      rw [IsSl2Triple.h_eq_coroot hα ht heα hfα, map_smul, subtype_apply]
  · have aux {β : Weight K H L} (hβ : β.IsNonZero) {y g : L}
        (hy : y ∈ genWeightSpace L β) (hg : g ∈ rootSpace H β) (hg_ne_zero : g ≠ 0) :
        ∃ c : K, y = c • g := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨g, hg⟩
        (by rwa [ne_eq, LieSubmodule.mk_eq_zero])).mp (LieAlgebra.IsKilling.finrank_rootSpace_eq_one β hβ) ⟨y, hy⟩
      exact ⟨c, by simpa using hc.symm⟩
    obtain ⟨x_αneg, hx_αneg, x_h, ⟨y, hy_coroot, rfl⟩, rfl⟩ := mem_sup.mp hx
    obtain ⟨x_pos, hx_pos, x_neg, hx_neg, rfl⟩ := mem_sup.mp hx_αneg
    obtain ⟨c₁, rfl⟩ := aux hα hx_pos heα ht.e_ne_zero
    obtain ⟨c₂, rfl⟩ := aux (Weight.IsNonZero.neg hα) hx_neg hfα ht.f_ne_zero
    obtain ⟨c₃, rfl⟩ : ∃ c₃ : K, c₃ • LieAlgebra.IsKilling.coroot α = y := by
      simpa [← mem_span_singleton, ← LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton α]
    change _ ∈ LieAlgebra.IsKilling.sl2SubalgebraOfRoot hα
    rw [LieAlgebra.IsKilling.mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
    use c₁, c₂, c₃
    simp [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, -LieSubmodule.incl_coe]

