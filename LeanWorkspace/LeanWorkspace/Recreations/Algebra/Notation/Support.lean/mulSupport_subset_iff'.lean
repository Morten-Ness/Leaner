import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_subset_iff' : Function.mulSupport f ⊆ s ↔ ∀ x ∉ s, f x = 1 := forall_congr' fun _ ↦ not_imp_comm

