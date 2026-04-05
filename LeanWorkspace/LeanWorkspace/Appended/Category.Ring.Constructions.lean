import Mathlib

section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem closure_range_union_range_eq_top_of_isPushout
    {R A B X : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B} {a : A ⟶ X} {b : B ⟶ X}
    (H : IsPushout f g a b) :
    Subring.closure (Set.range a ∪ Set.range b) = ⊤ := by
  algebraize [f.hom, g.hom]
  let e := ((CommRingCat.isPushout_tensorProduct R A B).isoIsPushout _ _ H).commRingCatIsoToRingEquiv
  rw [← Subring.comap_map_eq_self_of_injective e.symm.injective (.closure _), RingHom.map_closure,
    ← top_le_iff, ← Subring.map_le_iff_le_comap, Set.image_union]
  simp only [AlgHom.toRingHom_eq_coe, ← Set.range_comp, ← RingHom.coe_comp]
  rw [← hom_comp, ← hom_comp, IsPushout.inl_isoIsPushout_inv, IsPushout.inr_isoIsPushout_inv,
    hom_ofHom, hom_ofHom]
  exact le_top.trans (Algebra.TensorProduct.closure_range_union_range_eq_top R A B).ge

end

section

variable {A B : CommRingCat.{u}} (f g : A ⟶ B)

theorem equalizer_ι_isLocalHom (F : WalkingParallelPair ⥤ CommRingCat.{u}) :
    IsLocalHom (limit.π F WalkingParallelPair.zero).hom := by
  have := limMap_π (diagramIsoParallelPair F).hom WalkingParallelPair.zero
  rw [← IsIso.comp_inv_eq] at this
  rw [← this]
  rw [← limit.isoLimitCone_hom_π
      ⟨_,
        CommRingCat.equalizerForkIsLimit (F.map WalkingParallelPairHom.left)
          (F.map WalkingParallelPairHom.right)⟩
      WalkingParallelPair.zero]
  change IsLocalHom ((lim.map _ ≫ _ ≫ (CommRingCat.equalizerFork _ _).ι) ≫ _).hom
  infer_instance

end

section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

set_option backward.isDefEq.respectTransparency false in
theorem isPushout_iff_isPushout {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    IsPushout (ofHom <| algebraMap R R') (ofHom <| algebraMap R S)
      (ofHom <| algebraMap R' S') (ofHom <| algebraMap S S') ↔ Algebra.IsPushout R R' S S' := by
  refine ⟨fun h ↦ ?_, fun h ↦ CommRingCat.isPushout_of_isPushout ..⟩
  let e : R' ⊗[R] S ≃+* S' := ((CommRingCat.isPushout_tensorProduct R R' S).isoPushout ≪≫
      h.isoPushout.symm).commRingCatIsoToRingEquiv
  have h2 (r : R') : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (r ⊗ₜ 1) = (pushout.inl (ofHom _) (ofHom _)) r :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inl_isoPushout_hom).hom r)
  have h3 (x : R') := congr($(h.inl_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h3
  let e' : R' ⊗[R] S ≃ₐ[R'] S' := {
    __ := e
    commutes' r := by simp [Iso.commRingCatIsoToRingEquiv, h2, e, h3] }
  refine Algebra.IsPushout.of_equiv e' ?_
  ext s
  have h1 : (CommRingCat.isPushout_tensorProduct R R' S).isoPushout.hom
      (algebraMap S (R' ⊗[R] S) s) = (pushout.inr (ofHom _) (ofHom _)) s :=
    congr($((CommRingCat.isPushout_tensorProduct R R' S).inr_isoPushout_hom).hom s)
  have h4 (x : S) := congr($(h.inr_isoPushout_inv) x)
  dsimp only [hom_comp, RingHom.coe_comp, Function.comp_apply, hom_ofHom] at h4
  simp [Iso.commRingCatIsoToRingEquiv, h1, e', e, h4]

end

section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem isPushout_of_isLocalization {R S Rₘ Sₘ : Type u}
    [CommRing R] [CommRing Rₘ] [Algebra R Rₘ] [CommRing S] [CommRing Sₘ] [Algebra S Sₘ]
    (f : R →+* S) (fₘ : Rₘ →+* Sₘ) (H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).comp f)
    (M : Submonoid R) [IsLocalization M Rₘ] [IsLocalization (M.map f) Sₘ] :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (algebraMap R Rₘ))
      (CommRingCat.ofHom (algebraMap S Sₘ)) (CommRingCat.ofHom fₘ) := by
  algebraize [f, fₘ, fₘ.comp (algebraMap R Rₘ)]
  have : IsScalarTower R S Sₘ := .of_algebraMap_eq' H
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ := ‹_›
  exact CommRingCat.isPushout_iff_isPushout.mpr (Algebra.isPushout_of_isLocalization M _ _ _)

end

section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem isPushout_of_isPushout (R S A B : Type u) [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] :
    IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R A))
      (ofHom (algebraMap S B)) (ofHom (algebraMap A B)) := (CommRingCat.isPushout_tensorProduct R S A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Algebra.IsPushout.equiv R S A B).toCommRingCatIso (by simp) (by simp)
    (by ext; simp [Algebra.IsPushout.equiv_tmul]) (by ext; simp [Algebra.IsPushout.equiv_tmul])

end

section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

theorem isPushout_tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    IsPushout (ofHom <| algebraMap R A) (ofHom <| algebraMap R B)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := A ⊗[R] B) <| Algebra.TensorProduct.includeRight.toRingHom) where
  w := by
    ext
    simp
  isColimit' := ⟨CommRingCat.pushoutCoconeIsColimit R A B⟩

end

section

theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X := (hX.uniqueUpToIso CommRingCat.punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)

end
