import Mathlib

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable (b' : Basis ι' R M')

theorem prod_apply (i) :
    b.prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i := by
  ext <;> cases i <;>
    simp only [Module.Basis.prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, Module.Basis.prod_apply_inr_fst,
      Sum.elim_inr, LinearMap.inr_apply, Module.Basis.prod_apply_inl_snd, Module.Basis.prod_apply_inr_snd, Function.comp]

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable (b' : Basis ι' R M')

theorem prod_apply_inl_fst (i) : (b.prod b' (Sum.inl i)).1 = b i := b.repr.injective <| by
    ext j
    simp only [Module.Basis.prod, Module.Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b.repr.apply_symm_apply,
      LinearEquiv.symm_symm, repr_self, Finsupp.fst_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inl_injective

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable (b' : Basis ι' R M')

theorem prod_apply_inl_snd (i) : (b.prod b' (Sum.inl i)).2 = 0 := b'.repr.injective <| by
    ext j
    simp only [Module.Basis.prod, Module.Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b'.repr.apply_symm_apply,
      LinearEquiv.symm_symm, Finsupp.snd_sumFinsuppLEquivProdFinsupp,
      map_zero, Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inr_ne_inl

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable (b' : Basis ι' R M')

theorem prod_apply_inr_fst (i) : (b.prod b' (Sum.inr i)).1 = 0 := b.repr.injective <| by
    ext i
    simp only [Module.Basis.prod, Module.Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b.repr.apply_symm_apply,
      LinearEquiv.symm_symm, Finsupp.fst_sumFinsuppLEquivProdFinsupp,
      map_zero, Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inl_ne_inr

end

section

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable (b' : Basis ι' R M')

theorem prod_apply_inr_snd (i) : (b.prod b' (Sum.inr i)).2 = b' i := b'.repr.injective <| by
    ext i
    simp only [Module.Basis.prod, Module.Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b'.repr.apply_symm_apply,
      LinearEquiv.symm_symm, repr_self, Finsupp.snd_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inr_injective

end
