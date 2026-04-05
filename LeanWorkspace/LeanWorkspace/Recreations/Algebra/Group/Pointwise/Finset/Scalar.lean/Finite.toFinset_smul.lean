import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [SMul α β] [DecidableEq β] {s : Set α} {t : Set β}

theorem Finite.toFinset_smul (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht) :
    hf.toFinset = hs.toFinset • ht.toFinset :=
  Finite.toFinset_image2 _ _ _

