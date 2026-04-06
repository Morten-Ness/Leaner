import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_of_mem_val_ofUnits (S : Subgroup Mˣ) {y : Mˣ} (hy : (y : M) ∈ S.ofUnits) : y ∈ S := by
  rcases hy with ⟨x, hx, hxy⟩
  exact Units.ext hxy ▸ hx
