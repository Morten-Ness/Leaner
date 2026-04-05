import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem exists_lt (f : CauSeq α abs) : ∃ a : α, CauSeq.const a < f := let ⟨a, h⟩ := CauSeq.exists_gt (-f)
  ⟨-a, show CauSeq.Pos _ by rwa [CauSeq.const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩

-- so named to match `rat_add_continuous_lemma`

