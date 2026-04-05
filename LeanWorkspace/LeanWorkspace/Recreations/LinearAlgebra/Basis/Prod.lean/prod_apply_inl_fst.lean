import Mathlib

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

