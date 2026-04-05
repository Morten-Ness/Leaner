import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} (α : M ⟶ K) (β : Cochain M L (-1))
  (hαβ : δ (-1) 0 β + Cochain.ofHom (α ≫ φ) = 0)

theorem lift_fst :
    CochainComplex.mappingCocone.lift φ α β hαβ ≫ CochainComplex.mappingCocone.fst φ = α := by
  cat_disch

