import Mathlib

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

theorem degreewiseEpiWithInjectiveKernel_p :
    degreewiseEpiWithInjectiveKernel (p K L) := by
  intro n
  rw [epiWithInjectiveKernel_iff]
  refine ⟨(mappingCone (𝟙 (CochainComplex.cm5b.I K))).X n, inferInstance,
    (biprod.inl :_ ⟶ (mappingCone (𝟙 (CochainComplex.cm5b.I K))) ⊞ L).f n, ?_,
    (biprod.fst : (mappingCone (𝟙 (CochainComplex.cm5b.I K))) ⊞ L ⟶ _).f n,
    (biprod.inr :_ ⟶ (mappingCone (𝟙 (CochainComplex.cm5b.I K))) ⊞ L).f n, ?_, ?_, ?_⟩
  all_goals simp [← HomologicalComplex.comp_f, ← HomologicalComplex.add_f_apply]

