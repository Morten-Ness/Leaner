import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem rightUnshift_comp {m : ℤ} {a : ℤ} (γ' : CochainComplex.HomComplex.Cochain L (M⟦a⟧) m) {nm : ℤ} (hnm : n + m = nm)
    (nm' : ℤ) (hnm' : nm + a = nm') (m' : ℤ) (hm' : m + a = m') :
    (γ.comp γ' hnm).rightUnshift nm' hnm' =
      γ.comp (γ'.rightUnshift m' hm') (by lia) := by
  ext p q hpq
  rw [CochainComplex.HomComplex.Cochain.rightUnshift_v (γ.comp γ' hnm) nm' hnm' p q hpq (p + n + m) (by lia),
    γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl,
    comp_v _ _ (show n + m' = nm' by lia) p (p + n) q (by lia) (by lia),
    γ'.rightUnshift_v m' hm' (p + n) q (by lia) (p + n + m) rfl, assoc]

