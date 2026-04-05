import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem mk_v (CochainComplex.HomComplex.Cochain.v : ∀ (p q : ℤ) (_ : p + n = q), F.X p ⟶ G.X q) (p q : ℤ) (hpq : p + n = q) :
    (CochainComplex.HomComplex.Cochain.mk CochainComplex.HomComplex.Cochain.v).v p q hpq = CochainComplex.HomComplex.Cochain.v p q hpq := rfl

