import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

variable (i f) [Fact <| Function.Injective i]

set_option backward.privateInPublic true in
private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ∃ (a : (Module.Baer.extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩


theorem extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) :
    (Module.Baer.extensionOfMax i f).domain = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  dsimp
  rw [← Module.Baer.extensionOfMax_is_max i f _ (Module.Baer.extensionOfMax_le i f h), Module.Baer.extensionOfMaxAdjoin,
    Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩

