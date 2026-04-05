import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

variable (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
theorem exact_tfae : List.TFAE
    [
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).ShortExact,
      ∀ (S : ShortComplex C), S.Exact → (S.map F).Exact,
      PreservesHomology F,
      PreservesFiniteLimits F ∧ PreservesFiniteColimits F
    ] := by
  tfae_have 1 → 3
  | hF => by
    refine ⟨fun {X Y} f ↦ ?_, fun {X Y} f ↦ ?_⟩
    · have h := (CategoryTheory.Functor.preservesFiniteLimits_tfae F |>.out 0 2 |>.1 fun S hS ↦
        And.intro (hF S hS).exact (hF S hS).mono_f)
      exact h f
    · have h := (CategoryTheory.Functor.preservesFiniteColimits_tfae F |>.out 0 2 |>.1 fun S hS ↦
        And.intro (hF S hS).exact (hF S hS).epi_g)
      exact h f
  tfae_have 2 → 1
  | hF, S, hS => by
    have : Mono (S.map F).f := exact_iff_mono _ (by simp) |>.1 <|
      hF (.mk (0 : 0 ⟶ S.X₁) S.f <| by simp) (exact_iff_mono _ (by simp) |>.2 hS.mono_f)
    have : Epi (S.map F).g := exact_iff_epi _ (by simp) |>.1 <|
      hF (.mk S.g (0 : S.X₃ ⟶ 0) <| by simp) (exact_iff_epi _ (by simp) |>.2 hS.epi_g)
    exact ⟨hF S hS.exact⟩
  tfae_have 3 → 4
  | h => ⟨CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology F,
      CategoryTheory.Functor.preservesFiniteColimits_of_preservesHomology F⟩
  tfae_have 4 → 2
  | ⟨h1, h2⟩, _, h => h.map F
  tfae_finish

