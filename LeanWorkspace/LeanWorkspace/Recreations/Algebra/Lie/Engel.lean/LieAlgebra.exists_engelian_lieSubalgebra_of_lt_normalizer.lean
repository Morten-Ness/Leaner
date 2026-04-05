import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer {K : LieSubalgebra R L}
    (hK₁ : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K) (hK₂ : K < K.normalizer) :
    ∃ (K' : LieSubalgebra R L), LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K' ∧ K < K' := by
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.exists_of_lt hK₂
  let K' : LieSubalgebra R L :=
    { (R ∙ x) ⊔ (K : Submodule R L) with
      lie_mem' := fun {y z} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hx₁ }
  have hxK' : x ∈ K' := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
  have hKK' : K ≤ K' := (LieSubalgebra.toSubmodule_le_toSubmodule K K').mp le_sup_right
  have hK' : K' ≤ K.normalizer := by
    rw [← LieSubalgebra.toSubmodule_le_toSubmodule]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) hK₂.le
  refine ⟨K', ?_, lt_iff_le_and_ne.mpr ⟨hKK', fun contra => hx₂ (contra.symm ▸ hxK')⟩⟩
  intro M _i1 _i2 _i3 _i4 h
  obtain ⟨I, hI₁ : (I : LieSubalgebra R K') = LieSubalgebra.ofLe hKK'⟩ :=
    LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer hKK' hK'
  have hI₂ : R ∙ (⟨x, hxK'⟩ : K') ⊔ LieSubmodule.toSubmodule I = ⊤ := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule R K' I, hI₁]
    apply Submodule.map_injective_of_injective (K' : Submodule R L).injective_subtype
    simp only [LieSubalgebra.coe_ofLe, Submodule.map_sup, Submodule.map_subtype_range_inclusion,
      Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_subtype_span_singleton]
  have e : K ≃ₗ⁅R⁆ I :=
    (LieSubalgebra.equivOfLe hKK').trans
      (LieEquiv.ofEq _ _ ((LieSubalgebra.coe_set_eq _ _).mpr hI₁.symm))
  have hI₃ : LieAlgebra.IsEngelian R I := e.isEngelian_iff.mp hK₁
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop hI₂ (h _) (hI₃ _ fun x => h x)

attribute [local instance] LieSubalgebra.subsingleton_bot

