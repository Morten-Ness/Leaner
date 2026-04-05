import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mem_of_mulIndicator_ne_one (h : Set.mulIndicator s f a ≠ 1) : a ∈ s := not_imp_comm.1 (fun hn => Set.mulIndicator_of_notMem hn f) h

