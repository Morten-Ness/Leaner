import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

variable (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
theorem preservesFiniteLimits_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ (S : ShortComplex C), S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f),
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F,
      PreservesFiniteLimits F
    ] := by
  tfae_have 1 → 2
  | hF, S, ⟨hS, hf⟩ => by
    have := CategoryTheory.Functor.preservesMonomorphisms_of_preserves_shortExact_left F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero)
    let φ : T.map F ⟶ S.map F :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := F.map <| Abelian.factorThruCoimage S.g
        comm₂₃ := show 𝟙 _ ≫ F.map _ = F.map (cokernel.π _) ≫ _ by
          rw [Category.id_comp, ← F.map_comp, cokernel.π_desc] }
    exact (exact_iff_of_epi_of_isIso_of_mono φ).1 (hF T ⟨(S.exact_iff_exact_coimage_π).1 hS⟩).1
  tfae_have 2 → 3
  | hF, X, Y, f => by
    refine preservesLimit_of_preserves_limit_cone (kernelIsKernel f) ?_
    apply (KernelFork.isLimitMapConeEquiv _ F).2
    let S := ShortComplex.mk _ _ (kernel.condition f)
    let hS := hF S ⟨exact_kernel f, inferInstance⟩
    have : Mono (S.map F).f := hS.2
    exact hS.1.fIsKernel
  tfae_have 3 → 4
  | hF => by
    exact preservesFiniteLimits_of_preservesKernels F
  tfae_have 4 → 1
  | ⟨_⟩, S, hS =>
    (S.map F).exact_and_mono_f_iff_f_is_kernel |>.2 ⟨KernelFork.mapIsLimit _ hS.fIsKernel F⟩
  tfae_finish

