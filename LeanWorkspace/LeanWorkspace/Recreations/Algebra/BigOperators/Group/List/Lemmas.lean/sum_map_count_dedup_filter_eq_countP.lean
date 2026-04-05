import Mathlib

variable {ι α β M N P G : Type*}

variable [DecidableEq α]

theorem sum_map_count_dedup_filter_eq_countP (p : α → Bool) (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).sum = l.countP p := by
  induction l with
  | nil => simp
  | cons a as h =>
    simp_rw [List.countP_cons, List.count_cons, List.sum_map_add]
    congr 1
    · refine _root_.trans ?_ h
      by_cases ha : a ∈ as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_notMem ha, List.filter]
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · simp only [beq_iff_eq]
      by_cases hp : p a
      · refine _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h.symm]) ?_
        simp [hp, count_dedup]
      · exact _root_.trans (List.sum_eq_zero fun n hn => by grind) (by simp [hp])

