import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem fromSingleMk_surjective {p n : ℤ} (α : CochainComplex.HomComplex.Cocycle ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) (q' : ℤ) (hq' : q + 1 = q') :
    ∃ (f : X ⟶ K.X q) (hf : f ≫ K.d q q' = 0), CochainComplex.HomComplex.Cocycle.fromSingleMk f h q' hq' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf, Cochain.δ_fromSingleMk _ _ _ q' (by lia)] at hα
  replace hα := Cochain.congr_v hα p q' (by lia)
  exact ⟨f, by simpa using hα, by ext : 1; assumption⟩

