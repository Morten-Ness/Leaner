import Mathlib

variable {G H I : Type*}

variable [Group G] [Group H] [Group I]

set_option linter.existingAttributeWarning false in
theorem mem_graph {f : G →* H} {x : G × H} : x ∈ f.graph ↔ f x.1 = x.2 := .rfl

