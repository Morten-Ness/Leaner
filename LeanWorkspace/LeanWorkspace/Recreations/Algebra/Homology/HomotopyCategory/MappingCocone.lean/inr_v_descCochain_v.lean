import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

set_option backward.isDefEq.respectTransparency false in
theorem inr_v_descCochain_v (p q : ℤ) (hpq : p + 1 = q) (r : ℤ) (hr : q + m = r) :
    (CochainComplex.mappingCocone.inr φ).1.v p q hpq ≫ (CochainComplex.mappingCocone.descCochain φ α β h).v q r hr = β.v p r (by lia) := by
  obtain rfl : p = q + -1 := by lia
  simp [CochainComplex.mappingCocone.inr, CochainComplex.mappingCocone.descCochain, CochainComplex.mappingCocone, smul_smul,
    Cochain.rightShift_v _ _ _ _ _ _ hpq _ (add_zero (q + -1)),
    Cochain.leftShift_v (n := n) _ _ _ _ _ r _ (q + -1) (by lia)]

