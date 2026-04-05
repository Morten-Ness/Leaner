import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem δ_single {p q : ℤ} (f : K.X p ⟶ L.X q) (n m : ℤ) (hm : n + 1 = m)
    (p' q' : ℤ) (hp' : p' + 1 = p) (hq' : q + 1 = q') :
    CochainComplex.HomComplex.δ n m (CochainComplex.HomComplex.Cochain.single f n) = CochainComplex.HomComplex.Cochain.single (f ≫ L.d q q') m + m.negOnePow • CochainComplex.HomComplex.Cochain.single (K.d p' p ≫ f) m := by
  ext p'' q'' hpq''
  rw [CochainComplex.HomComplex.δ_v n m hm (CochainComplex.HomComplex.Cochain.single f n) p'' q'' (by lia) (q'' - 1) (p'' + 1) rfl (by lia),
    CochainComplex.HomComplex.Cochain.add_v, CochainComplex.HomComplex.Cochain.units_smul_v]
  congr 1
  · by_cases h : p'' = p
    · subst h
      by_cases h : q = q'' - 1
      · subst h
        obtain rfl : q' = q'' := by lia
        simp only [CochainComplex.HomComplex.Cochain.single_v]
      · rw [CochainComplex.HomComplex.Cochain.single_v_eq_zero', CochainComplex.HomComplex.Cochain.single_v_eq_zero', zero_comp]
        all_goals lia
    · rw [CochainComplex.HomComplex.Cochain.single_v_eq_zero _ _ _ _ _ h, CochainComplex.HomComplex.Cochain.single_v_eq_zero _ _ _ _ _ h, zero_comp]
  · subst hm
    by_cases h : q'' = q
    · subst h
      by_cases h : p'' = p'
      · subst h
        obtain rfl : p = p'' + 1 := by lia
        simp
      · rw [CochainComplex.HomComplex.Cochain.single_v_eq_zero _ _ _ _ _ h, CochainComplex.HomComplex.Cochain.single_v_eq_zero, comp_zero, smul_zero]
        lia
    · simp [CochainComplex.HomComplex.Cochain.single_v_eq_zero' _ _ _ _ _ h]

