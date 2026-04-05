import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {I : LieIdeal R L} {x : L} (hxI : R ∙ x ⊔ I = ⊤)

theorem lcs_le_lcs_of_is_nilpotent_span_sup_eq_top {n i j : ℕ}
    (hxn : toEnd R L M x ^ n = 0) (hIM : lowerCentralSeries R L M i ≤ I.lcs M j) :
    lowerCentralSeries R L M (i + n) ≤ I.lcs M (j + 1) := by
  suffices
    ∀ l,
      ((⊤ : LieIdeal R L).lcs M (i + l) : Submodule R M) ≤
        (I.lcs M j : Submodule R M).map (toEnd R L M x ^ l) ⊔
          (I.lcs M (j + 1) : Submodule R M)
    by simpa only [bot_sup_eq, LieIdeal.incl_coe, Submodule.map_zero, hxn] using this n
  intro l
  induction l with
  | zero =>
    simp only [add_zero, LieIdeal.lcs_succ, pow_zero, Module.End.one_eq_id,
      Submodule.map_id]
    exact le_sup_of_le_left hIM
  | succ l ih =>
    simp only [LieIdeal.lcs_succ, i.add_succ l, LieSubmodule.lie_top_eq_of_span_sup_eq_top hxI, sup_le_iff]
    refine ⟨(Submodule.map_mono ih).trans ?_, le_sup_of_le_right ?_⟩
    · rw [Submodule.map_sup, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← pow_succ', ←
        I.lcs_succ]
      grw [coe_map_toEnd_le]
    · norm_cast
      gcongr
      exact le_trans (antitone_lowerCentralSeries R L M le_self_add) hIM

