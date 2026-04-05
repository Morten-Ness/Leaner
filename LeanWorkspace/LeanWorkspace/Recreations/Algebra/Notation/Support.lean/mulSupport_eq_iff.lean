import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_eq_iff : Function.mulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1 := by
  simp +contextual only [Set.ext_iff, Function.mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]

