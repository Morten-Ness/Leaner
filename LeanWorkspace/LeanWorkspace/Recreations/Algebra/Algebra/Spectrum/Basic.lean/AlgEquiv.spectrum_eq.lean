import Mathlib

open scoped Pointwise Ring

theorem AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) (a : A) :
    spectrum R (f a) = spectrum R a := Set.Subset.antisymm (AlgHom.spectrum_apply_subset _ _) <| by
    simpa only [AlgEquiv.coe_algHom, AlgEquiv.coe_coe_symm_apply_coe_apply] using
      AlgHom.spectrum_apply_subset (f : A ≃ₐ[R] B).symm (f a)

