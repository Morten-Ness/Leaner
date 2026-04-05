import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

theorem ofHom_lift :
    Cochain.ofHom (CochainComplex.mappingCone.lift φ α β eq) = CochainComplex.mappingCone.liftCochain φ α β (zero_add 1) := by
  simp only [CochainComplex.mappingCone.lift, Cocycle.cochain_ofHom_homOf_eq_coe, liftCocycle_coe]

