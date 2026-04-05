import Mathlib

theorem boundaryLE_embeddingUpIntLE_iff (p : ℤ) (n : ℕ) :
    (embeddingUpIntLE p).BoundaryLE n ↔ n = 0 := by
  constructor
  · intro h
    obtain _ | n := n
    · rfl
    · have := h.2 n
      dsimp at this
      lia
  · rintro rfl
    constructor
    · simp
    · intro i hi
      dsimp at hi
      lia

