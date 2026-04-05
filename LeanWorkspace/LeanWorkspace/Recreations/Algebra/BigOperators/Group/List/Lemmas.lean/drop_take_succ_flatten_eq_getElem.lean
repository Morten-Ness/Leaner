import Mathlib

variable {ι α β M N P G : Type*}

theorem drop_take_succ_flatten_eq_getElem (L : List (List α)) (i : Nat) (h : i < L.length) :
    (L.flatten.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum = L[i] := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take, Nat.min_eq_left]
  simp only [this, take_sum_flatten, drop_sum_flatten,
    drop_take_succ_eq_cons_getElem, h, flatten_nil, flatten_cons, append_nil]

