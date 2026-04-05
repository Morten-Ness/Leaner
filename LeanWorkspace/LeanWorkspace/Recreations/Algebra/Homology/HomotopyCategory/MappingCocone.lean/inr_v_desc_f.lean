import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} (α : Cochain K M 0) (β : Cocycle L M 1)
  (hαβ : δ 0 1 α + (Cochain.ofHom φ).comp β.1 (zero_add 1) = 0)

theorem inr_v_desc_f (p q : ℤ) (hpq : p + 1 = q) :
    (CochainComplex.mappingCocone.inr φ).1.v p q hpq ≫ (CochainComplex.mappingCocone.desc φ α β hαβ).f q = β.1.v p q hpq := by
  simp [CochainComplex.mappingCocone.desc]

