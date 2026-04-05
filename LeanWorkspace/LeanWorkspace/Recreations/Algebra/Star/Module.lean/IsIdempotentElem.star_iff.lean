import Mathlib

theorem IsIdempotentElem.star_iff {R : Type*} [Mul R] [StarMul R] {a : R} :
    IsIdempotentElem (star a) ↔ IsIdempotentElem a := by
  simp [IsIdempotentElem, ← star_mul]

alias ⟨_, IsIdempotentElem.star⟩ := IsIdempotentElem.star_iff

