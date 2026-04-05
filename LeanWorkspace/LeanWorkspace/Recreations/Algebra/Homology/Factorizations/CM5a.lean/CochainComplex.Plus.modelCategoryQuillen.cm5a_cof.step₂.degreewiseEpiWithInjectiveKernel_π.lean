import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem degreewiseEpiWithInjectiveKernel_π :
    degreewiseEpiWithInjectiveKernel (π f n) := by
  intro CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i
  rw [epiWithInjectiveKernel_iff]
  exact ⟨_, inferInstance, (mappingCocone.inr (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)).1.v (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i - 1) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (by lia), by simp,
    ⟨{r := (mappingCocone.snd (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)).v _ _ (by lia)
      s := (mappingCocone.inl (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)).v _ _ (by lia)
      id := (add_comm _ _).trans (by simp [mappingCocone.id_X]) }⟩⟩

