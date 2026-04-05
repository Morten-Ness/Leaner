import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem existsUnique : ∃! p, CharP R p := let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

