import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem mul_limZero_right (f : CauSeq β abv) {g} (hg : CauSeq.LimZero g) : CauSeq.LimZero (f * g)
  | ε, ε0 =>
    let ⟨F, F0, hF⟩ := CauSeq.bounded' f 0
    (hg _ <| div_pos ε0 F0).imp fun _ H j ij => by
      have := mul_lt_mul' (le_of_lt <| hF j) (H _ ij) (abv_nonneg abv _) F0
      rwa [mul_comm F, div_mul_cancel₀ _ (ne_of_gt F0), ← abv_mul] at this

