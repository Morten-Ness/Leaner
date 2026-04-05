import Mathlib

variable {A R : Type*} [AddGroup A] [Fintype A] [CommSemiring R] [IsDomain R]
  {ψ : AddChar A R}

theorem sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] :
    ∑ a, ψ a = if ψ = 0 then ↑(card A) else 0 := by
  split_ifs with h
  · simp [h]
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.1 h
  refine eq_zero_of_mul_eq_self_left hx ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y ↦ (AddChar.map_add_eq_mul ..).symm

