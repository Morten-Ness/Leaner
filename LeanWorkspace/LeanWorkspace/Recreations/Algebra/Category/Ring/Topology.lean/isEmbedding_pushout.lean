import Mathlib

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

set_option backward.isDefEq.respectTransparency false in
theorem isEmbedding_pushout [IsTopologicalRing R] (φ : A ⟶ B) (ψ : A ⟶ C) :
    IsEmbedding fun f : pushout φ ψ ⟶ R ↦ (pushout.inl φ ψ ≫ f, pushout.inr φ ψ ≫ f) := by
  -- The key idea: Let `X = Spec B` and `Y = Spec C`.
  -- We want to show `(X × Y)(R)` has the subspace topology from `X(R) × Y(R)`.
  -- We already know that `X(R) × Y(R)` is a subspace of `𝔸ᴮ(R) × 𝔸ᶜ(R)` and by explicit calculation
  -- this is isomorphic to `𝔸ᴮ⁺ᶜ(R)` which `(X × Y)(R)` embeds into.
  let PB := CommRingCat.of (MvPolynomial B A)
  let PC := CommRingCat.of (MvPolynomial C A)
  let fB : PB ⟶ B := CommRingCat.ofHom (MvPolynomial.eval₂Hom φ.hom id)
  have hfB : Function.Surjective fB.hom := fun x ↦ ⟨.X x, by simp [PB, fB]⟩
  let fC : PC ⟶ C := CommRingCat.ofHom (MvPolynomial.eval₂Hom ψ.hom id)
  have hfC : Function.Surjective fC.hom := fun x ↦ ⟨.X x, by simp [PC, fC]⟩
  have := (CommRingCat.HomTopology.isEmbedding_precomp_of_surjective (R := R) fB hfB).prodMap
    (CommRingCat.HomTopology.isEmbedding_precomp_of_surjective (R := R) fC hfC)
  rw [← IsEmbedding.of_comp_iff this]
  let PBC := CommRingCat.of (MvPolynomial (B ⊕ C) A)
  let fBC : PBC ⟶ pushout φ ψ :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (φ ≫ pushout.inl φ ψ).hom
      (Sum.elim (pushout.inl φ ψ).hom (pushout.inr φ ψ).hom))
  have hfBC : Function.Surjective fBC := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← closure_range_union_range_eq_top_of_isPushout (.of_hasPushout _ _), Subring.closure_le]
    simp only [Set.union_subset_iff, RingHom.coe_range, Set.range_subset_iff, Set.mem_range]
    exact ⟨fun x ↦ ⟨.X (.inl x), by simp [fBC, PBC]⟩, fun x ↦ ⟨.X (.inr x), by simp [fBC, PBC]⟩⟩
  let F : ((A ⟶ R) × ((B ⊕ C) → R)) → ((A ⟶ R) × (B → R)) × ((A ⟶ R) × (C → R)) :=
    fun x ↦ ⟨⟨x.1, x.2 ∘ Sum.inl⟩, ⟨x.1, x.2 ∘ Sum.inr⟩⟩
  have hF : IsEmbedding F := (Homeomorph.prodProdProdComm _ _ _ _).isEmbedding.comp
    ((isEmbedding_graph continuous_id).prodMap Homeomorph.sumArrowHomeomorphProdArrow.isEmbedding)
  have H := (CommRingCat.HomTopology.mvPolynomialHomeomorph B R A).symm.isEmbedding.prodMap
    (CommRingCat.HomTopology.mvPolynomialHomeomorph C R A).symm.isEmbedding
  convert ((H.comp hF).comp (CommRingCat.HomTopology.mvPolynomialHomeomorph _ R A).isEmbedding).comp
    (CommRingCat.HomTopology.isEmbedding_precomp_of_surjective (R := R) fBC hfBC)
  have (s : _) : (pushout.inr φ ψ).hom (ψ.hom s) = (pushout.inl φ ψ).hom (φ.hom s) :=
    congr($(pushout.condition (f := φ)).hom s).symm
  ext f s <;> simp [fB, fC, fBC, PB, PC, PBC, F, this]

