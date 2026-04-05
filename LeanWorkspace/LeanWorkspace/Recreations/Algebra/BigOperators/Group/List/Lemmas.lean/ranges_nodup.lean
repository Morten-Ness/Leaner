import Mathlib

variable {ι α β M N P G : Type*}

theorem ranges_nodup {l s : List ℕ} (hs : s ∈ ranges l) : s.Nodup := (List.pairwise_flatten.mp <| by rw [List.ranges_flatten]; exact nodup_range).1 s hs

