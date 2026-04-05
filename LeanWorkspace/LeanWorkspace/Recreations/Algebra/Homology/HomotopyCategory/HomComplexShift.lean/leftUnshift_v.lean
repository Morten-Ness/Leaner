import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

variable (γ γ₁ γ₂ : Cochain K L n)

theorem leftUnshift_v {n' a : ℤ} (γ : CochainComplex.HomComplex.Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p' + n' = q) :
    (γ.leftUnshift n hn).v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p' p (by lia)).inv ≫ γ.v p' q (by lia) := by
  obtain rfl : p' = p - a := by lia
  rfl

