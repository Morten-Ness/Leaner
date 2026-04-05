import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctor_map_f' {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map φ).f p = φ.f (p + n) := rfl

