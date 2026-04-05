import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] {s t : Set α}

theorem Finite.toFinset_mul (hs : s.Finite) (ht : t.Finite) (hf := hs.mul ht) :
    hf.toFinset = hs.toFinset * ht.toFinset :=
  Finite.toFinset_image2 _ _ _

