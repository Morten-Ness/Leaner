import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem mul_limZero_left {f} (g : CauSeq β abv) (hg : CauSeq.LimZero f) : CauSeq.LimZero (f * g)
  | ε, ε0 =>
    let ⟨G, G0, hG⟩ := CauSeq.bounded' g 0
    (hg _ <| div_pos ε0 G0).imp fun _ H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _)
      rwa [div_mul_cancel₀ _ (ne_of_gt G0), ← abv_mul] at this

