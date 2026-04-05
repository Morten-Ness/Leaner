import Mathlib

variable (R : Type u)

variable [Ring R]

set_option backward.isDefEq.respectTransparency false in
theorem uliftFunctor_map_exact (S : ShortComplex (ModuleCat.{v} R)) (h : S.Exact) :
    (S.map (ModuleCat.uliftFunctor R)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  dsimp [ModuleCat.uliftFunctor]
  intro x
  simp only [Function.comp_apply, Set.mem_range, LinearEquiv.symm_apply_eq, map_zero]
  rw [(CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h]
  cat_disch

