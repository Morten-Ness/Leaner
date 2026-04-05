import Mathlib

variable {α β : Type*} [Neg α]

variable {γ : Type*}

theorem Even.left_comp {g : α → β} (hg : g.Even) (f : β → γ) : (f ∘ g).Even := (congr_arg f <| hg ·)

