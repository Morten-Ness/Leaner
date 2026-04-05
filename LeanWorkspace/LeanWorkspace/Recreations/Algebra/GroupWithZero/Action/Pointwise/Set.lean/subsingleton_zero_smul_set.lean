import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton := subsingleton_singleton.anti <| Set.zero_smul_set_subset s

