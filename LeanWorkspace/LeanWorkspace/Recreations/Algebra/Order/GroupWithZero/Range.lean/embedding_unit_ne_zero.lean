import Mathlib

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

theorem embedding_unit_ne_zero (a : (MonoidWithZeroHom.ValueGroup₀ f)ˣ) :
    embedding a.1 ≠ 0 := (MonoidWithZeroHom.ValueGroup₀.embedding_unit_pos a).ne.symm

