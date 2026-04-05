import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} (α : Cochain K M 0) (β : Cocycle L M 1)
  (hαβ : δ 0 1 α + (Cochain.ofHom φ).comp β.1 (zero_add 1) = 0)

theorem ofHom_desc :
    Cochain.ofHom (CochainComplex.mappingCocone.desc φ α β hαβ) = CochainComplex.mappingCocone.descCochain φ α β.1 (by lia) := by
  simp [CochainComplex.mappingCocone.desc]

