import Mathlib

variable {ι α β M N P G : Type*}

variable [DecidableEq α]

theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).sum = l.length := by
  simpa using List.sum_map_count_dedup_filter_eq_countP (fun _ => True) l

