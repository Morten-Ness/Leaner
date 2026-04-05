import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem exact_homologyShortComplex [Mono f] :
    (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.homologyShortComplex f n).Exact := by
  let T := ShortComplex.mk (homologyMap f n) (homologyMap (cokernel.π f) n)
    (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])
  let φ : T ⟶ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.homologyShortComplex f n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := homologyMap ((cokernel f).πTruncGE n ≫ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.p f n) n
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, ← homologyMap_comp, CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α] }
  obtain ⟨_, _, _⟩ : Mono φ.τ₃ ∧ IsIso φ.τ₂ ∧ Epi φ.τ₁ := by
    dsimp [φ]
    rw [homologyMap_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.shortExact f).homology_exact₂ n

