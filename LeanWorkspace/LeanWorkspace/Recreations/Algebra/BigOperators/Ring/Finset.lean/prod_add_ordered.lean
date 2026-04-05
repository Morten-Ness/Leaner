import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

theorem prod_add_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i + g i) =
      (∏ i ∈ s, f i) +
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j + g j)) * ∏ j ∈ s with i < j, f j := by
  refine Finset.induction_on_max s (by simp) ?_
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => lt_irrefl a (ha a ha')
  rw [prod_insert ha', prod_insert ha', sum_insert ha', filter_insert, if_neg (lt_irrefl a),
    filter_true_of_mem ha, ihs, add_mul, mul_add, mul_add, add_assoc]
  congr 1
  rw [add_comm]
  congr 1
  · rw [filter_false_of_mem, prod_empty, mul_one]
    exact (forall_mem_insert _ _ _).2 ⟨lt_irrefl a, fun i hi => (ha i hi).not_gt⟩
  · rw [Finset.mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [filter_insert, if_neg (ha i hi).not_gt, filter_insert, if_pos (ha i hi), prod_insert,
      mul_left_comm]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'

