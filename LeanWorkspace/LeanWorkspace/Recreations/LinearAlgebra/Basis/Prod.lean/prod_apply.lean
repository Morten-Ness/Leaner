import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

variable (b' : Basis ι' R M')

theorem prod_apply (i) :
    b.prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i := by
  ext <;> cases i <;>
    simp only [Module.Basis.prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, Module.Basis.prod_apply_inr_fst,
      Sum.elim_inr, LinearMap.inr_apply, Module.Basis.prod_apply_inl_snd, Module.Basis.prod_apply_inr_snd, Function.comp]

