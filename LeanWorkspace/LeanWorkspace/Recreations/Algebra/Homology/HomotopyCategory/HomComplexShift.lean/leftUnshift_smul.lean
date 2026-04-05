import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftUnshift_smul {n' a : ℤ} (γ : CochainComplex.HomComplex.Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') (x : R) :
    (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn := by
  change (CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

