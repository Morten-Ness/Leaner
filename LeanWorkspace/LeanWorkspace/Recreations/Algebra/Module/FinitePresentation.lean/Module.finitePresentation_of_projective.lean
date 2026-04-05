import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem Module.finitePresentation_of_projective [Projective R M] [Module.Finite R M] :
    FinitePresentation R M := have ⟨_n, _f, _g, surj, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  Module.finitePresentation_of_free_of_surjective _ surj
    (LinearMap.ker_eq_range_of_comp_eq_id hfg ▸ .of_finite)

