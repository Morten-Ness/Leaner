import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} {n m : ℤ}

variable (α : Cochain K F m) (β : Cochain K G n) (h : n + 1 = m)

theorem liftCochain_fst :
    (CochainComplex.mappingCone.liftCochain φ α β h).comp (CochainComplex.mappingCone.fst φ).1 h = α := by
  simp [CochainComplex.mappingCone.liftCochain]

