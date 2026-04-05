import Mathlib

variable (C : Type*) [Category* C]

variable {C} [Preadditive C]

variable {K L : CochainComplex C ℤ} {f g : K ⟶ L}

theorem homotopyUnop_hom_eq
    (h : Homotopy ((CochainComplex.opEquivalence C).functor.map f.op)
      ((CochainComplex.opEquivalence C).functor.map g.op))
    (p q p' q' : ℤ) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (CochainComplex.homotopyUnop h).hom p q =
      (K.XIsoOfEq (by dsimp; lia)).hom ≫ (h.hom q' p').unop ≫
        (L.XIsoOfEq (by dsimp; lia)).hom := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [CochainComplex.homotopyUnop]

