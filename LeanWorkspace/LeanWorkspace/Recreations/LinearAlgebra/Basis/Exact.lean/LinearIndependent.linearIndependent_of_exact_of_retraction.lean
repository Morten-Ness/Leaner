import Mathlib

variable {R M K P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup K] [AddCommGroup P]

variable [Module R M] [Module R K] [Module R P]

variable {f : K →ₗ[R] M} {g : M →ₗ[R] P} {s : M →ₗ[R] K}

variable (hs : s ∘ₗ f = LinearMap.id) (hfg : Function.Exact f g)

variable {ι κ σ : Type*} {v : ι → M} {a : κ → ι} {b : σ → ι}

theorem LinearIndependent.linearIndependent_of_exact_of_retraction
    (hainj : Function.Injective a) (hsa : ∀ i, s (v (a i)) = 0)
    (hli : LinearIndependent R v) :
    LinearIndependent R (g ∘ v ∘ a) := by
  apply (LinearIndependent.comp hli a hainj).map
  rw [Submodule.disjoint_def, hfg.linearMap_ker_eq]
  rintro - hy ⟨y, rfl⟩
  have hz : s (f y) = 0 := by
    revert hy
    generalize f y = x
    intro hy
    induction hy using Submodule.span_induction with
    | mem m hm => obtain ⟨i, rfl⟩ := hm; apply hsa
    | zero => simp_all
    | add => simp_all
    | smul => simp_all
  replace hs := DFunLike.congr_fun hs y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
  rw [← hs, hz, map_zero]

