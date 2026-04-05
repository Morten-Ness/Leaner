import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

theorem inr_comp_descCochain :
    (CochainComplex.mappingCocone.inr φ).1.comp (CochainComplex.mappingCocone.descCochain φ α β h) (by lia) = β := by
  ext p q hpq
  simp [Cochain.comp_v (n₂ := m) _ _ _ _ (p + 1) q rfl (by lia)]

