import Mathlib

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem Odd.sum_eq_zero [Fintype α] [InvolutiveNeg α] {f : α → β} (hf : f.Odd) : ∑ a, f a = 0 := hf.finset_sum_eq_zero <| Finset.map_univ_equiv (Equiv.neg α)

