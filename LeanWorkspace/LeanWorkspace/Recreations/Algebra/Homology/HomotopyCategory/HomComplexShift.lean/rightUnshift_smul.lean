import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem rightUnshift_smul {n' a : ℤ} (γ : CochainComplex.HomComplex.Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) (x : R) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  change (CochainComplex.HomComplex.Cochain.rightShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

