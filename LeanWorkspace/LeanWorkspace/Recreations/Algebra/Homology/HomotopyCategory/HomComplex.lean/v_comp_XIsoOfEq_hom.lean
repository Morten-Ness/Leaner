import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem v_comp_XIsoOfEq_hom
    (γ : CochainComplex.HomComplex.Cochain F G n) (p q q' : ℤ) (hpq : p + n = q) (hq' : q = q') :
    γ.v p q hpq ≫ (HomologicalComplex.XIsoOfEq G hq').hom = γ.v p q' (by rw [← hq', hpq]) := by
  subst hq'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, comp_id]

