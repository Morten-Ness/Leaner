import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)

theorem δ_liftCochain (m' : ℤ) (hm' : m + 1 = m') :
    δ n m (CochainComplex.mappingCone.liftCochain φ α β h) = -(δ m m' α).comp (CochainComplex.mappingCone.inl φ) (by lia) +
      (δ n m β + α.comp (Cochain.ofHom φ) (add_zero m)).comp
        (Cochain.ofHom (CochainComplex.mappingCone.inr φ)) (add_zero m) := by
  dsimp only [CochainComplex.mappingCone.liftCochain]
  simp only [δ_add, δ_comp α (CochainComplex.mappingCone.inl φ) _ m' _ _ h hm' (neg_add_cancel 1),
    δ_comp_zero_cochain _ _ _ h, CochainComplex.mappingCone.δ_inl, Cochain.ofHom_comp,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    δ_ofHom, Cochain.comp_zero, zero_add, Cochain.add_comp,
    Cochain.comp_assoc_of_second_is_zero_cochain]
  abel

