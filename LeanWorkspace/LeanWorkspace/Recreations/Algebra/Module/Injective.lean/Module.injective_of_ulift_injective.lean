import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {M : Type v} [AddCommGroup M] [Module R M]

set_option backward.privateInPublic true in
private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ∃ (a : (Module.Baer.extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩


theorem Module.injective_of_ulift_injective
    (inj : Module.Injective R (ULift.{v'} M)) :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g := let eX := ULift.moduleEquiv.{_, _, v'} (R := R) (M := X)
    have ⟨g', hg'⟩ := inj.out (ULift.moduleEquiv.{_, _, v'}.symm.toLinearMap ∘ₗ f ∘ₗ eX.toLinearMap)
      (by exact ULift.Module.Baer.injective moduleEquiv.symm.comp <| hf.comp Module.Baer.injective eX)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMap)
    ⟨ULift.moduleEquiv.toLinearMap ∘ₗ g' ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
      fun x ↦ by exact Module.Baer.congr(ULift.down $(hg' ⟨x⟩))⟩

