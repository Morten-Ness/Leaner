FAIL
import Mathlib

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

theorem injective_iff_injective_object :
    Module.Injective R M ↔
    CategoryTheory.Injective (ModuleCat.of R M) := by
  rw [Module.Injective]
  constructor
  · intro h
    intro J _ _ i f
    rw [ModuleCat.mono_iff_injective] at i
    let f' : M →ₗ[R] J := f
    rcases h i f' with ⟨g', hg'⟩
    refine ⟨g', ?_⟩
    ext x
    exact congrArg (fun k => k x) hg'
  · intro h
    intro J N i f
    let i' : ModuleCat.of R N ⟶ ModuleCat.of R J := i
    have hi' : Mono i' := by
      rw [ModuleCat.mono_iff_injective]
      exact i
    let f' : ModuleCat.of R M ⟶ ModuleCat.of R J := f
    rcases h.factor_thru f' i' with ⟨g', hg'⟩
    refine ⟨g', ?_⟩
    ext x
    exact congrArg (fun k => k x) hg'
