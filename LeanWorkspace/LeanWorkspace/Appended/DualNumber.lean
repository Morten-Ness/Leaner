import Mathlib

section

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem algHom_ext ⦃f g : R[ε] →ₐ[R] A⦄ (hε : f ε = g ε) : f = g := by
  ext
  dsimp
  simp only [one_smul, hε]

end

section

variable {R A B : Type*}

theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := (DualNumber.commute_eps_left x).symm

end

section

variable {R A B : Type*}

theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) := ext (mul_zero r).symm (mul_one r).symm

end

section

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem lift_inlAlgHom_eps :
    DualNumber.lift ⟨(inlAlgHom _ _ _, ε), DualNumber.eps_mul_eps, fun _ => DualNumber.commute_eps_left _⟩ = AlgHom.id R A[ε] := DualNumber.lift.apply_symm_apply <| AlgHom.id R A[ε]

end

section

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

end

section

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem range_lift
    (fe : {fe : (A →ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ ∀ a, Commute fe.2 (fe.1 a)}) :
    (DualNumber.lift fe).range = fe.1.1.range ⊔ R[fe.1.2] := by
  simp_rw [← Algebra.map_top, ← DualNumber.range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]

end

section

variable {R A B : Type*}

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem ringHom_ext {R' : Type*} [CommSemiring R'] {f g : R[ε] →+* R'}
    (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g := by
  letI : Algebra R R' := by
    letI := f.toAlgebra
    exact Algebra.compHom _ (algebraMap R R[ε])
  let f' : R[ε] →ₐ[R] R' :=
    { toRingHom := f
      commutes' _ := rfl }
  let g' : R[ε] →ₐ[R] R' :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  exact congr_arg AlgHom.toRingHom (show f' = g' from DualNumber.algHom_ext hε)

end
