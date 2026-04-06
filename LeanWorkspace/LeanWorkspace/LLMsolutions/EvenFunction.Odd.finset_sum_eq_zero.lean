FAIL
import Mathlib

variable {α β : Type*} [Neg α]

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

theorem Odd.finset_sum_eq_zero [InvolutiveNeg α] {f : α → β} (hf : f.Odd) {s : Finset α}
    (hs : Finset.map (Equiv.neg α).toEmbedding s = s) :
    s.sum f = 0 := by
  have hsum_neg : (Finset.map (Equiv.neg α).toEmbedding s).sum f = s.sum (fun x => f (-x)) := by
    simp [Finset.sum_map]
  have h1 : s.sum f = s.sum (fun x => f (-x)) := by
    calc
      s.sum f = (Finset.map (Equiv.neg α).toEmbedding s).sum f := by rw [hs]
      _ = s.sum (fun x => f (-x)) := hsum_neg
  have h2 : s.sum f = -s.sum f := by
    calc
      s.sum f = s.sum (fun x => f (-x)) := h1
      _ = s.sum (fun x => -f x) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [hf x]
      _ = -s.sum f := by simp
  have h3 : s.sum f + s.sum f = 0 := by
    calc
      s.sum f + s.sum f = s.sum f + (-s.sum f) := by rw [h2]
      _ = 0 := add_right_neg _
  have h4 : (2 : ℕ) • s.sum f = 0 := by
    simpa [two_nsmul] using h3
  exact (nsmul_right_injective two_ne_zero) <| by simpa using h4
