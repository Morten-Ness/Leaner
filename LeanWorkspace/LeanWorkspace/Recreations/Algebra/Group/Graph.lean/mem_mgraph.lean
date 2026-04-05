import Mathlib

variable {G H I : Type*}

variable [Monoid G] [Monoid H] [Monoid I]

set_option linter.existingAttributeWarning false in
theorem mem_mgraph {f : G →* H} {x : G × H} : x ∈ f.mgraph ↔ f x.1 = x.2 := .rfl

