import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKInjective_of_injective_aux {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Function.Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n + 1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by lia) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by lia)
  have hu : K.d n (n + 1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by lia) (by lia), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; lia)] at hK
  obtain ⟨β, hβ⟩ : ∃ (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by lia
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by lia) (by lia), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia),
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by lia) n (n + 2)
      (by lia) (by lia), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by lia)]
    simp [hβ, u]

