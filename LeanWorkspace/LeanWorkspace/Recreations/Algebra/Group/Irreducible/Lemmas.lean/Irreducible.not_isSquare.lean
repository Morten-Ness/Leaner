import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem Irreducible.not_isSquare (ha : Irreducible x) : ¬IsSquare x := by
  rw [isSquare_iff_exists_sq]
  rintro ⟨y, rfl⟩
  exact not_irreducible_pow (by decide) ha

