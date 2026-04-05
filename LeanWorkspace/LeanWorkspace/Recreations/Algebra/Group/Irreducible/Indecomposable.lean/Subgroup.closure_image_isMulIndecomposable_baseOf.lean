import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem Subgroup.closure_image_isMulIndecomposable_baseOf [Finite ι] [InvolutiveInv ι]
    [CommGroup S] [IsOrderedMonoid S]
    (v : ι → G) (hv_inv : ∀ i, v i⁻¹ = (v i)⁻¹)
    (f : G →* S) (hf : ∀ i, f (v i) ≠ 1) :
    closure (v '' IsMulIndecomposable.baseOf v f) = closure (Set.range v) := by
  rw [← image_univ]
  refine le_antisymm (closure_mono (image_mono <| by simp)) ((closure_le _).mpr ?_)
  have : Set.univ = {i | 1 < f (v i)} ∪ {i | f (v i) < 1} := by ext i; simp [(hf i).symm]
  rw [this, image_union, union_subset_iff]
  refine ⟨le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f)), ?_⟩
  · simp [Submonoid.closure_image_isMulIndecomposable_baseOf]
  · let f' : G →* S := invMonoidHom.comp f
    have h₁ : (invMonoidHom ∘ v) '' IsMulIndecomposable.baseOf v f' =
        v '' IsMulIndecomposable.baseOf v f := by
      rw [image_comp, IsMulIndecomposable.image_baseOf_inv_comp_eq v hv_inv f, image_comp,
        ← image_comp]
      simp
    have h₂ : v '' {i | f (v i) < 1} = v '' {i | 1 < f' (v i)} := by simp [f']
    rw [h₂, ← h₁, image_comp, coe_invMonoidHom, image_inv_eq_inv, closure_inv]
    refine le_trans ?_ (le_closure_toSubmonoid (v '' IsMulIndecomposable.baseOf v f'))
    simp [Submonoid.closure_image_isMulIndecomposable_baseOf]

