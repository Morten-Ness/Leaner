import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

variable {X : C} {K : CochainComplex C ℤ}

set_option backward.isDefEq.respectTransparency false in
theorem toSingleMk_mem_coboundaries_iff {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    (p'' : ℤ) (hp'' : p + 1 = p'') :
    CochainComplex.HomComplex.Cocycle.toSingleMk f h p' hp' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : K.X p'' ⟶ X), K.d p p'' ≫ g = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective α p'' (by lia)
    refine ⟨n.negOnePow • g, ?_⟩
    rw [← hg, toSingleMk_coe, Cochain.δ_toSingleMk _ _ _ _ h] at hα
    exact (Cochain.toSingleEquiv h).symm.injective (by simpa)
  · rintro ⟨g, rfl⟩
    exact ⟨n.negOnePow • Cochain.toSingleMk g (by lia),
      by simp [Cochain.δ_toSingleMk _ _ _ _ h, smul_smul]⟩

