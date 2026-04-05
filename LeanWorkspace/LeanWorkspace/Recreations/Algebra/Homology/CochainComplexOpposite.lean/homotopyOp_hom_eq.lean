import Mathlib

variable (C : Type*) [Category* C]

variable {C} [Preadditive C]

variable {K L : CochainComplex C ℤ} {f g : K ⟶ L}

theorem homotopyOp_hom_eq (h : Homotopy f g)
    (p q p' q' : ℤ) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (CochainComplex.homotopyOp h).hom p q =
      (L.XIsoOfEq (by dsimp; lia)).hom.op ≫ (h.hom q' p').op ≫
        (K.XIsoOfEq (by dsimp; lia)).hom.op := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [CochainComplex.homotopyOp]

