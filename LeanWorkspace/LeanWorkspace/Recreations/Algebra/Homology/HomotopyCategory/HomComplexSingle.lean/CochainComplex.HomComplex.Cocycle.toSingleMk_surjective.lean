import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem toSingleMk_surjective {q n : ℤ} (α : CochainComplex.HomComplex.Cocycle K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p) :
    ∃ (f : K.X p ⟶ X) (hf : K.d p' p ≫ f = 0), CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.toSingleMk_surjective α.1 p h
  have hα := ((n + 1).negOnePow • α).δ_eq_zero (n + 1)
  rw [coe_units_smul, δ_units_smul, ← hf, Cochain.δ_toSingleMk _ _ _ p' (by lia),
    smul_smul, Int.units_mul_self, one_smul] at hα
  refine ⟨f, ?_, ?_⟩
  · simpa [← cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv] using
    Cochain.congr_v hα p' q (by lia)
  · ext : 1; assumption

