import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V}
    (h : ¬AffineIndependent k ((↑) : t → V)) :
    ∃ f : V → k, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
    rw [affineIndependent_iff_of_fintype] at h
    simp only [exists_prop, not_forall] at h
    obtain ⟨w, hw, hwt, i, hi⟩ := h
    simp only [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w ((↑) : t → V) hw 0,
      vsub_eq_sub, Finset.weightedVSubOfPoint_apply, sub_zero] at hwt
    let f : ∀ x : V, x ∈ t → k := fun x hx => w ⟨x, hx⟩
    refine ⟨fun x => if hx : x ∈ t then f x hx else (0 : k), ?_, ?_, by use i; simp [f, hi]⟩
    on_goal 1 =>
      suffices (∑ e ∈ t, dite (e ∈ t) (fun hx => f e hx • e) fun _ => 0) = 0 by
        convert this
        rename V => x
        by_cases hx : x ∈ t <;> simp [hx]
    all_goals
      simp only [f, Finset.sum_dite_of_true fun _ h => h, Finset.mk_coe, hwt, hw]

