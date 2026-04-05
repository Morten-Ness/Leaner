import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_insertIdx {i} (hlen : i ≤ l.length) (hcomm : ∀ a' ∈ l.take i, Commute a a') :
    (l.insertIdx i a).prod = a * l.prod := by
  induction i generalizing l
  case zero => rfl
  case succ i ih =>
    obtain ⟨hd, tl, rfl⟩ := exists_cons_of_length_pos (Nat.zero_lt_of_lt hlen)
    simp only [insertIdx_succ_cons, prod_cons,
      ih (Nat.le_of_lt_succ hlen) (fun a' a'_mem => hcomm a' (mem_of_mem_tail a'_mem))]
    exact Commute.left_comm (hcomm hd (mem_of_mem_head? rfl)).symm tl.prod

