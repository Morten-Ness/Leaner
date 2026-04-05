import Mathlib

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

