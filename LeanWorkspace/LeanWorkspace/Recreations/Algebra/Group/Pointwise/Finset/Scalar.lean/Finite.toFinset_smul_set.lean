import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

theorem Finite.toFinset_smul_set (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set) :
    hf.toFinset = a • hs.toFinset :=
  Finite.toFinset_image _ _ _

