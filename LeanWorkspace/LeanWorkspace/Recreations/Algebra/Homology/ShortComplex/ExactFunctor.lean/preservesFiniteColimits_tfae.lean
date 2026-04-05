import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

variable (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
theorem preservesFiniteColimits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ (S : ShortComplex C), S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F,
      PreservesFiniteColimits F
    ] := by
  tfae_have 1 → 2
  | hF, S, ⟨hS, hf⟩ => by
    have := CategoryTheory.Functor.preservesEpimorphisms_of_preserves_shortExact_right F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map <| Abelian.factorThruImage S.f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := show _ ≫ F.map (kernel.ι _) = F.map _ ≫ 𝟙 _ by
          rw [← F.map_comp, Abelian.image.fac, Category.comp_id] }
    exact (exact_iff_of_epi_of_isIso_of_mono φ).2 (hF T ⟨(S.exact_iff_exact_image_ι).1 hS⟩).1
  tfae_have 2 → 3
  | hF, X, Y, f => by
    refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ F).2
    let S := ShortComplex.mk _ _ (cokernel.condition f)
    let hS := hF S ⟨exact_cokernel f, inferInstance⟩
    have : Epi (S.map F).g := hS.2
    exact hS.1.gIsCokernel
  tfae_have 3 → 4
  | hF => by
    exact preservesFiniteColimits_of_preservesCokernels F
  tfae_have 4 → 1
  | ⟨_⟩, S, hS => (S.map F).exact_and_epi_g_iff_g_is_cokernel |>.2
    ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel F⟩
  tfae_finish

