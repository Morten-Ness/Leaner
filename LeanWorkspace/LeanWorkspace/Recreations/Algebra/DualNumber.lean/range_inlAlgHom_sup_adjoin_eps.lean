import Mathlib

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem range_inlAlgHom_sup_adjoin_eps :
    (inlAlgHom R A A).range ⊔ Algebra.adjoin R {ε} = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq, DualNumber.inr_eq_smul_eps, ← inl_mul_eq_smul]
  refine add_mem ?_ (mul_mem ?_ ?_)
  · exact le_sup_left (α := Subalgebra R _) <| Set.mem_range_self x.fst
  · exact le_sup_left (α := Subalgebra R _) <| Set.mem_range_self x.snd
  · refine le_sup_right (α := Subalgebra R _) <| subset_adjoin <| Set.mem_singleton ε

