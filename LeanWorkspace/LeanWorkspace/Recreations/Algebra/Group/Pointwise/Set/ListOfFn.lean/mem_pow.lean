import Mathlib

variable {α : Type*} [Monoid α] {s : Set α} {n : ℕ}

theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i ↦ (f i : α)).prod = a := by
  rw [← Set.mem_prod_list_ofFn, List.ofFn_const, List.prod_replicate]

