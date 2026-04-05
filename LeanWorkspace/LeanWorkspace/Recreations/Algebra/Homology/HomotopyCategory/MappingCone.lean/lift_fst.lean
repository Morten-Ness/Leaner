import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

theorem lift_fst :
    (Cochain.ofHom (CochainComplex.mappingCone.lift φ α β eq)).comp (CochainComplex.mappingCone.fst φ).1 (zero_add 1) = α.1 := by simp

