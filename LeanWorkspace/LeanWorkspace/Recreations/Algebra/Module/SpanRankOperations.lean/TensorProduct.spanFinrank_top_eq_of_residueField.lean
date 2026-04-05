import Mathlib

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

variable [IsLocalRing R]

theorem TensorProduct.spanFinrank_top_eq_of_residueField (fg : N.FG) :
    (⊤ : Submodule 𝓀 (𝓀 ⊗[R] N)).spanFinrank = N.spanFinrank := by
  let : Module.Finite R N := Module.Finite.iff_fg.mpr fg
  apply (TensorProduct.spanFinrank_top_le_of_fg N fg).antisymm
  obtain ⟨s, hs₁, hs₂⟩ := (⊤ : Submodule 𝓀 (𝓀 ⊗[R] N)).exists_span_set_card_eq_spanRank
  have hs₃ : s.Finite := Cardinal.mk_lt_aleph0_iff.mp (by simpa [hs₁] using Module.Finite.fg_top)
  let t := Function.surjInv (mk_surjective R N 𝓀 residue_surjective) '' s
  have ht₁ : mk R 𝓀 N 1 '' t = s := by rw [← Set.image_comp, Function.comp_surjInv, s.image_id]
  have ht₂ : span R t = ⊤ := by
    rwa [← restrictScalars_eq_top_iff R, restrictScalars_span _ _ (by exact residue_surjective),
      ← ht₁, ← map_span, map_tensorProduct_mk_eq_top] at hs₂
  grw [← N.spanFinrank_top, ← ht₂, spanFinrank_span_le_ncard_of_finite (hs₃.image _), spanFinrank,
    ← hs₁, Set.ncard_image_le hs₃]
  rfl

