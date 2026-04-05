import Mathlib

variable {M A B : Type*}

variable [AddMonoid A]

theorem closure_singleton_eq (x : A) :
    closure ({x} : Set A) = AddMonoidHom.mrange (multiplesHom A x) := closure_eq_of_le (Set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩) fun _ ⟨_n, hn⟩ =>
    hn ▸ nsmul_mem (subset_closure <| Set.mem_singleton _) _

