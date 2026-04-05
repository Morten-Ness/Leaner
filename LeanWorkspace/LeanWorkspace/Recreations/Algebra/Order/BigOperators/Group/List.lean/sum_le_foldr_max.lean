import Mathlib

variable {ι α M N : Type*}

theorem sum_le_foldr_max [AddZeroClass M] [Zero N] [LinearOrder N] (f : M → N) (h0 : f 0 ≤ 0)
    (hadd : ∀ x y, f (x + y) ≤ max (f x) (f y)) (l : List M) : f l.sum ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => simpa using h0
  | cons hd tl IH =>
    simp only [List.sum_cons, List.foldr_map, List.foldr] at IH ⊢
    exact (hadd _ _).trans (max_le_max le_rfl IH)

