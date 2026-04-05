import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K L : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K F m) (β : Cochain K G n) {n' m' : ℤ} (α' : Cochain F L m') (β' : Cochain G L n')
  (h : n + 1 = m) (h' : m' + 1 = n') (p : ℤ) (hp : n + n' = p)

theorem liftCochain_v_descCochain_v (p₁ p₂ p₃ : ℤ) (h₁₂ : p₁ + n = p₂) (h₂₃ : p₂ + n' = p₃)
    (q : ℤ) (hq : p₁ + m = q) :
    (CochainComplex.mappingCone.liftCochain φ α β h).v p₁ p₂ h₁₂ ≫ (CochainComplex.mappingCone.descCochain φ α' β' h').v p₂ p₃ h₂₃ =
      α.v p₁ q hq ≫ α'.v q p₃ (by omega) + β.v p₁ p₂ h₁₂ ≫ β'.v p₂ p₃ h₂₃ := by
  have eq := Cochain.congr_v (CochainComplex.mappingCone.liftCochain_descCochain φ α β α' β' h h' p hp) p₁ p₃ (by lia)
  simpa only [Cochain.comp_v _ _ hp p₁ p₂ p₃ h₁₂ h₂₃, Cochain.add_v,
    Cochain.comp_v _ _ _ _ _ _ hq (show q + m' = p₃ by lia)] using eq

