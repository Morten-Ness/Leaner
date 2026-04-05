import Mathlib

variable (R : Type u) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]

theorem Module.FinitePresentation.equiv_quotient [Module.FinitePresentation R M] [Small.{v} R] :
    ∃ (L : Type v) (_ : AddCommGroup L) (_ : Module R L) (K : Submodule R L)
      (_ : M ≃ₗ[R] L ⧸ K), Module.Free R L ∧ Module.Finite R L ∧ K.FG := have ⟨_n, _K, e, fg⟩ := Module.FinitePresentation.exists_fin R M
  let es := Shrink.linearEquiv
  ⟨_, inferInstance, inferInstance, _, e ≪≫ₗ Submodule.Quotient.equiv _ _ (es ..).symm rfl,
    .of_equiv (es ..).symm, .equiv (es ..).symm, fg.map (es ..).symm.toLinearMap⟩

