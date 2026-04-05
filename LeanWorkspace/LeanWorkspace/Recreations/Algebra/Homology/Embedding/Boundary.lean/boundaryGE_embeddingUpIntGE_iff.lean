import Mathlib

theorem boundaryGE_embeddingUpIntGE_iff (p : ℤ) (n : ℕ) :
    (embeddingUpIntGE p).BoundaryGE n ↔ n = 0 := by
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

