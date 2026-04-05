import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

set_option backward.isDefEq.respectTransparency false in
theorem rightShift_rightUnshift {a n' : ℤ} (γ : CochainComplex.HomComplex.Cochain K (L⟦a⟧) n') (n : ℤ) (hn' : n' + a = n) :
    (γ.rightUnshift n hn').rightShift a n' hn' = γ := by
  ext p q hpq
  simp only [CochainComplex.HomComplex.Cochain.rightShift_v (γ.rightUnshift n hn') a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

