import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

theorem Set.preimage_one {α β : Type*} [One β] (s : Set β) [Decidable ((1 : β) ∈ s)] :
    (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then Set.univ else ∅ := Set.preimage_const 1 s

