import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

theorem fromSingleMk_mem_coboundaries_iff {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0)
    (q'' : ℤ) (hq'' : q'' + 1 = q) :
    CochainComplex.HomComplex.Cocycle.fromSingleMk f h q' hq' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : X ⟶ K.X q''), g ≫ K.d q'' q = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by lia)
    refine ⟨g, ?_⟩
    rw [← hg, fromSingleMk_coe, Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by lia), Cochain.δ_fromSingleMk _ _ _ _ h⟩

