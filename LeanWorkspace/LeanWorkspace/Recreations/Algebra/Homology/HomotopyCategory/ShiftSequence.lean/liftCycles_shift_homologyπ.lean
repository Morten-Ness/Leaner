import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable [CategoryWithHomology C]

set_option backward.isDefEq.respectTransparency false in
theorem liftCycles_shift_homologyπ
    (K : CochainComplex C ℤ) {A : C} {n i : ℤ} (f : A ⟶ (K⟦n⟧).X i) (j : ℤ)
    (hj : (up ℤ).next i = j) (hf : f ≫ (K⟦n⟧).d i j = 0) (i' : ℤ) (hi' : n + i = i') (j' : ℤ)
    (hj' : (up ℤ).next i' = j') :
    (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i =
      K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by lia)).hom) j' hj' (by
        simp only [next] at hj hj'
        obtain rfl : i' = i + n := by lia
        obtain rfl : j' = j + n := by lia
        dsimp at hf ⊢
        simp only [Linear.comp_units_smul] at hf
        apply (one_smul (M := ℤˣ) _).symm.trans _
        rw [← Int.units_mul_self n.negOnePow, mul_smul, comp_id, hf, smul_zero]) ≫
        K.homologyπ i' ≫
          ((HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftIso n i i' hi').inv.app K := by
  simp only [liftCycles, homologyπ,
    shiftFunctorObjXIso, Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    ShiftSequence.shiftIso_inv_app, ShortComplex.homologyπ_naturality,
    ShortComplex.liftCycles_comp_cyclesMap_assoc, shiftShortComplexFunctorIso_inv_app_τ₂,
    assoc, Iso.hom_inv_id, comp_id]
  rfl

