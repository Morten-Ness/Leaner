import Mathlib

section

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] [HasZeroObject C]

theorem alternatingConst_exactAt (X : C) (n : ℕ) (hn : n ≠ 0) :
    (ChainComplex.alternatingConst.obj X).ExactAt n := by
  rcases n.even_or_odd with h | h
  · exact ⟨(ChainComplex.alternatingConstHomologyDataEvenNEZero X _ h hn), isZero_zero C⟩
  · exact ⟨(ChainComplex.alternatingConstHomologyDataOdd X _ h), isZero_zero C⟩

end

section

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

variable {c : ComplexShape ℕ} [DecidableRel c.Rel] (hc : ∀ i j, c.Rel i j → Odd (i + j))

set_option backward.isDefEq.respectTransparency false in
theorem alternatingConst_iCycles_even_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (HomologicalComplex.alternatingConst A hOdd hEven hc).iCycles j ≫ φ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (HomologicalComplex.alternatingConstScIsoEven A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, HomologicalComplex.alternatingConstScIsoEven,
    Category.id_comp (X := (HomologicalComplex.alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk ψ φ hEven).iCycles_g

end

section

variable {C : Type*} [Category* C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

variable {c : ComplexShape ℕ} [DecidableRel c.Rel] (hc : ∀ i j, c.Rel i j → Odd (i + j))

set_option backward.isDefEq.respectTransparency false in
theorem alternatingConst_iCycles_odd_comp [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (HomologicalComplex.alternatingConst A hOdd hEven hc).iCycles j ≫ ψ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso
    (HomologicalComplex.alternatingConstScIsoOdd A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, HomologicalComplex.alternatingConstScIsoOdd,
    Category.id_comp (X := (HomologicalComplex.alternatingConst A hOdd hEven hc).X _)]
    using (ShortComplex.mk φ ψ hOdd).iCycles_g

end
