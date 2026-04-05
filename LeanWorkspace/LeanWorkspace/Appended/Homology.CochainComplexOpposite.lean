import Mathlib

section

variable (C : Type*) [Category* C]

variable {C} [Preadditive C]

theorem acyclic_op {K : CochainComplex C ℤ} (hK : K.Acyclic) :
   ((CochainComplex.opEquivalence C).functor.obj (op K)).Acyclic := fun n ↦ CochainComplex.exactAt_op (hK (-n)) n

end

section

variable (C : Type*) [Category* C]

variable {C} [Preadditive C]

theorem exactAt_op {K : CochainComplex C ℤ} {n : ℤ} (hK : K.ExactAt n)
    (m : ℤ) (hm : n + m = 0 := by lia) :
    ((CochainComplex.opEquivalence C).functor.obj (op K)).ExactAt m := by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp),
    ← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [prev])
    (by grind [next])] at hK

end

section

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

end

section

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

end
