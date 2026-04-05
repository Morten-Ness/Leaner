import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem id_X (p q : ℤ) (hpq : p + 1 = q) :
    (CochainComplex.mappingCone.fst φ).1.v p q hpq ≫ (CochainComplex.mappingCone.inl φ).v q p (by lia) +
      (CochainComplex.mappingCone.snd φ).v p p (add_zero p) ≫ (CochainComplex.mappingCone.inr φ).f p = 𝟙 ((CochainComplex.mappingCone φ).X p) := by
  simpa only [Cochain.add_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, id_f,
    Cochain.comp_v _ _ (add_neg_cancel 1) p q p hpq (by lia)]
    using Cochain.congr_v (CochainComplex.mappingCone.id φ) p p (add_zero p)

