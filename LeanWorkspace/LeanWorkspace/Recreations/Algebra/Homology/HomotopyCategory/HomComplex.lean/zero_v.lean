import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem zero_v {n : ℤ} (p q : ℤ) (hpq : p + n = q) :
    (0 : CochainComplex.HomComplex.Cochain F G n).v p q hpq = 0 := rfl

