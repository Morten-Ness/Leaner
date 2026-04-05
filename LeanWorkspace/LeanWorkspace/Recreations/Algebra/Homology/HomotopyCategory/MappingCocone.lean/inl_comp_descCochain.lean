import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

theorem inl_comp_descCochain :
    (CochainComplex.mappingCocone.inl φ).comp (CochainComplex.mappingCocone.descCochain φ α β h) (zero_add m) = α := by
  cat_disch

