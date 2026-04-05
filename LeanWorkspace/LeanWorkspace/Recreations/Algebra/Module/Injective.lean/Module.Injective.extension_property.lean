import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable (R : Type uR) [Ring R] [Small.{uM} R]

variable (M : Type uM) [AddCommGroup M] [Module R M] [inj : Module.Injective R M]

variable (P : Type uP) [AddCommGroup P] [Module R P]

variable (P' : Type uP') [AddCommGroup P'] [Module R P']

set_option backward.privateInPublic true in
private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ∃ (a : (Module.Baer.extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩


theorem Module.Injective.extension_property
    (f : P →ₗ[R] P') (hf : Function.Injective f)
    (g : P →ₗ[R] M) : ∃ h : P' →ₗ[R] M, h ∘ₗ f = g := Module.Baer.extension_property (Module.Baer.of_injective inj) f hf g

