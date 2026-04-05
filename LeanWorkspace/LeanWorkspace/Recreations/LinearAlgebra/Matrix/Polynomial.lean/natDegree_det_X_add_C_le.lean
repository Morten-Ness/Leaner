import Mathlib

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

theorem natDegree_det_X_add_C_le (A B : Matrix n n α) :
    natDegree (det ((Polynomial.X : α[Polynomial.X]) • A.map Polynomial.C + B.map Polynomial.C : Matrix n n α[Polynomial.X])) ≤ Fintype.card n := by
  rw [Matrix.det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    natDegree (sign g • ∏ i : n, (Polynomial.X • A.map Polynomial.C + B.map Polynomial.C : Matrix n n α[Polynomial.X]) (g i) i) ≤
        natDegree (∏ i : n, (Polynomial.X • A.map Polynomial.C + B.map Polynomial.C : Matrix n n α[Polynomial.X]) (g i) i) := by
      rcases Int.units_eq_one_or (sign g) with sg | sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i : n, natDegree (((Polynomial.X : α[Polynomial.X]) • A.map Polynomial.C + B.map Polynomial.C : Matrix n n α[Polynomial.X]) (g i) i) :=
      (natDegree_prod_le (Finset.univ : Finset n) fun i : n =>
        (Polynomial.X • A.map Polynomial.C + B.map Polynomial.C : Matrix n n α[Polynomial.X]) (g i) i)
    _ ≤ Finset.univ.card • 1 := (Finset.sum_le_card_nsmul _ _ 1 fun (i : n) _ => ?_)
    _ ≤ Fintype.card n := by simp [mul_one, Finset.card_univ]
  dsimp only [add_apply, smul_apply, Matrix.map_apply, smul_eq_mul]
  compute_degree

