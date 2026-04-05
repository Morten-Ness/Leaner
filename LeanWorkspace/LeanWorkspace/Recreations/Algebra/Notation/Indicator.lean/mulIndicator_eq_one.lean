import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_eq_one : (Set.mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSupport f) s := by
  simp only [funext_iff, Set.mulIndicator_apply_eq_one, Set.disjoint_left, mem_mulSupport,
    not_imp_not]

