import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x ∈ S.op ↔ x.unop ∈ S := Iff.rfl

