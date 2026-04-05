import Mathlib

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem Odd.finset_sum_eq_zero [InvolutiveNeg α] {f : α → β} (hf : f.Odd) {s : Finset α}
    (hs : Finset.map (Equiv.neg α).toEmbedding s = s) :
    s.sum f = 0 := by
  simpa [neg_eq_self, funext hf, hs] using (Finset.sum_map s (Equiv.neg α).toEmbedding f).symm

