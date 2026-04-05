import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

theorem toFinset_smul_set (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)] :
    (a • s).toFinset = a • s.toFinset := toFinset_image _ _

