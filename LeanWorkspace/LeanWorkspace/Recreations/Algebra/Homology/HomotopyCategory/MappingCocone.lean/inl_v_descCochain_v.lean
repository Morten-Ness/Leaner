import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n)

set_option backward.isDefEq.respectTransparency false in
theorem inl_v_descCochain_v (p q : ℤ) (hpq : p + m = q) :
    (CochainComplex.mappingCocone.inl φ).v p p (add_zero _) ≫ (CochainComplex.mappingCocone.descCochain φ α β h).v p q hpq = α.v p q hpq := by
  simp [CochainComplex.mappingCocone.inl, CochainComplex.mappingCocone.descCochain, CochainComplex.mappingCocone,
    Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia), smul_smul,
    Cochain.leftShift_v (n := n) _ (-1) m (by lia) _ _ hpq (p + -1) (by lia)]

