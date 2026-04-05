import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {I : LieIdeal R L} {x : L} (hxI : R ∙ x ⊔ I = ⊤)

theorem isNilpotentOfIsNilpotentSpanSupEqTop (hnp : IsNilpotent <| toEnd R L M x)
    (hIM : IsNilpotent I M) : IsNilpotent L M := by
  obtain ⟨n, hn⟩ := hnp
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R I M
  have hk' : I.lcs M k = ⊥ := by
    simp only [← toSubmodule_inj, I.coe_lcs_eq, hk, bot_toSubmodule]
  suffices ∀ l, lowerCentralSeries R L M (l * n) ≤ I.lcs M l by
    rw [isNilpotent_iff R]
    use k * n
    simpa [hk'] using this k
  intro l
  induction l with
  | zero => simp
  | succ l ih => exact (l.succ_mul n).symm ▸ LieSubmodule.lcs_le_lcs_of_is_nilpotent_span_sup_eq_top hxI hn ih

