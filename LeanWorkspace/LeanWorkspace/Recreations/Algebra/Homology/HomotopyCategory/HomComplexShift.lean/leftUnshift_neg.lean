import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftUnshift_neg {n' a : ℤ} (γ : CochainComplex.HomComplex.Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    (-γ).leftUnshift n hn = -γ.leftUnshift n hn := by
  change (CochainComplex.HomComplex.Cochain.leftShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

