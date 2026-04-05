import Mathlib

variable {M : Type*}

theorem associated_one_iff_isUnit [Monoid M] {a : M} : (a : M) ~ᵤ 1 ↔ IsUnit a := Iff.intro
    (fun h =>
      let ⟨c, h⟩ := Associated.symm h
      h ▸ ⟨c, Associated.symm (one_mul _)⟩)
    fun ⟨c, h⟩ => Associated.symm ⟨c, by simp [h]⟩

