import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [VSub α β] {s t : Set β}

theorem Finite.toFinset_vsub (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht) :
    hf.toFinset = hs.toFinset -ᵥ ht.toFinset :=
  Finite.toFinset_image2 _ _ _

