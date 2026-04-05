import Mathlib

variable {F α β γ : Type*}

variable [SMul α β] {s : Set β} {a : α}

theorem Finite.smul_set : s.Finite → (a • s).Finite := Finite.image _

