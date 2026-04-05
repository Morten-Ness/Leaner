import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

theorem smul_set_insert (a : α) (b : β) (s : Set β) : a • insert b s = insert (a • b) (a • s) := image_insert_eq ..

