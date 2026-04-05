import Mathlib

variable {α : Type*} [Monoid α] {s : Set α} {n : ℕ}

theorem mem_list_prod {l : List (Set α)} {a : α} :
    a ∈ l.prod ↔
      ∃ l' : List (Σ s : Set α, ↥s),
        List.prod (l'.map fun x ↦ (Sigma.snd x : α)) = a ∧ l'.map Sigma.fst = l := by
  induction l using List.ofFnRec with | _ n f
  simp only [Set.mem_prod_list_ofFn, List.exists_iff_exists_tuple, List.map_ofFn, List.ofFn_inj',
    Sigma.mk.inj_iff, and_left_comm, exists_and_left, exists_eq_left, heq_eq_eq]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i ↦ ⟨_, fi i⟩, rfl, rfl⟩
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i ↦ _, rfl⟩

