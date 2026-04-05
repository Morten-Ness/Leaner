import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem XIsoOfEq_shift (K : CochainComplex C ℤ) (n : ℤ) {p q : ℤ} (hpq : p = q) :
    (K⟦n⟧).XIsoOfEq hpq = K.XIsoOfEq (show p + n = q + n by rw [hpq]) := rfl

