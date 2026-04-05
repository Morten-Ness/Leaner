import Mathlib

variable {α : Type*} [Monoid α] {s : Set α} {n : ℕ}

theorem mem_prod_list_ofFn {a : α} {s : Fin n → Set α} :
    a ∈ (List.ofFn s).prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i ↦ (f i : α)).prod = a := by
  induction n generalizing a with
  | zero => simp_rw [List.ofFn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
  | succ n ih =>
    simp_rw [List.ofFn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_exists_eq_and, SetCoe.exists, exists_prop]

