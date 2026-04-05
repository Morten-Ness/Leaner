import Mathlib

variable {F α β γ : Type*}

variable [SMul α β] {s : Set β} {a : α}

theorem Infinite.of_smul_set : (a • s).Infinite → s.Infinite := Infinite.of_image _

