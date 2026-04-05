import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := Set.one_mem_inv_mul_iff.not_left

alias ⟨_, _root_.Disjoint.one_notMem_div_set⟩ := Set.one_notMem_div_iff

attribute [to_additive] Disjoint.one_notMem_div_set

