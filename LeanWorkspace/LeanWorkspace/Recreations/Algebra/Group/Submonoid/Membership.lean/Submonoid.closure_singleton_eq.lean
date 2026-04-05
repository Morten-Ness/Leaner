import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem closure_singleton_eq (x : M) : closure ({x} : Set M) = mrange (powersHom M x) := closure_eq_of_le (Set.singleton_subset_iff.2 ⟨Multiplicative.ofAdd 1, pow_one x⟩) fun _ ⟨_, hn⟩ =>
    hn ▸ pow_mem (subset_closure <| Set.mem_singleton _) _

