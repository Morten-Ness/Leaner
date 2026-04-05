import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem image_one {f : α → β} : f '' 1 = {f 1} := image_singleton

