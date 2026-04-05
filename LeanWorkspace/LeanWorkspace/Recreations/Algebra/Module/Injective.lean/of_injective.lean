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


theorem of_injective [Small.{v} R] (inj : Module.Injective R Q) : Module.Baer R Q := by
  intro I g
  let eI := Shrink.linearEquiv R I
  let eR := Shrink.linearEquiv R R
  obtain ⟨g', hg'⟩ := Module.Injective.out (eR.symm.toLinearMap ∘ₗ I.subtype ∘ₗ eI.toLinearMap)
    (Module.Baer.injective eR.symm.comp <| Subtype.val_injective.comp Module.Baer.injective eI) (g ∘ₗ eI.toLinearMap)
  exact ⟨g' ∘ₗ eR.symm.toLinearMap, fun x mx ↦ by simpa [eI, eR] using hg' (equivShrink I ⟨x, mx⟩)⟩

