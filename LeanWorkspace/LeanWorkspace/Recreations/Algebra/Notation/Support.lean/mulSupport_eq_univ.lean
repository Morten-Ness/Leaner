import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_eq_univ (hf : ∀ x, f x ≠ 1) : Function.mulSupport f = Set.univ := Set.eq_univ_of_forall hf

