import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem neg_v {n : ℤ} (z : CochainComplex.HomComplex.Cochain F G n) (p q : ℤ) (hpq : p + n = q) :
    (-z).v p q hpq = -(z.v p q hpq) := rfl

