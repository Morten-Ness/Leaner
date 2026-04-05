import Mathlib

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

