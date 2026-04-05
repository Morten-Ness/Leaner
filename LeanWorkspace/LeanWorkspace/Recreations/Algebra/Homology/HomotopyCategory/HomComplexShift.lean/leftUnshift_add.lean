import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftUnshift_add {n' a : ℤ} (γ₁ γ₂ : CochainComplex.HomComplex.Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    (γ₁ + γ₂).leftUnshift n hn = γ₁.leftUnshift n hn + γ₂.leftUnshift n hn := by
  change (CochainComplex.HomComplex.Cochain.leftShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

