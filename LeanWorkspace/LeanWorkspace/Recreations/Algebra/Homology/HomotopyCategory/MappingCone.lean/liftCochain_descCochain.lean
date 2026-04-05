import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K L : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K F m) (β : Cochain K G n) {n' m' : ℤ} (α' : Cochain F L m') (β' : Cochain G L n')
  (h : n + 1 = m) (h' : m' + 1 = n') (p : ℤ) (hp : n + n' = p)

theorem liftCochain_descCochain :
    (CochainComplex.mappingCone.liftCochain φ α β h).comp (CochainComplex.mappingCone.descCochain φ α' β' h') hp =
      α.comp α' (by lia) + β.comp β' (by lia) := by
  simp [CochainComplex.mappingCone.liftCochain, CochainComplex.mappingCone.descCochain,
    Cochain.comp_assoc α (CochainComplex.mappingCone.inl φ) _ _ (show -1 + n' = m' by lia) (by linarith)]

