import Mathlib

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

