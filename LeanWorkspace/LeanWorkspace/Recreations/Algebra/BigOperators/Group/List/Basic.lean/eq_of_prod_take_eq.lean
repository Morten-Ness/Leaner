import Mathlib

variable {ι α β M N P G : Type*}

theorem eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : ∀ i ≤ L.length, (L.take i).prod = (L'.take i).prod) : L = L' := by
  refine ext_get h fun i h₁ h₂ => ?_
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [List.prod_take_succ L i h₁, List.prod_take_succ L' i h₂, h' i (Nat.le_of_lt h₁)] at this
  convert mul_left_cancel this

