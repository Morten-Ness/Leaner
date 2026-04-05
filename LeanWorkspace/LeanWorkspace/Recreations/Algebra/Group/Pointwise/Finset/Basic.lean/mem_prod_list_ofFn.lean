import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem mem_prod_list_ofFn {a : α} {s : Fin n → Finset α} :
    a ∈ (List.ofFn s).prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a := by
  rw [← mem_coe, Finset.coe_list_prod, List.map_ofFn, Set.mem_prod_list_ofFn]
  rfl

