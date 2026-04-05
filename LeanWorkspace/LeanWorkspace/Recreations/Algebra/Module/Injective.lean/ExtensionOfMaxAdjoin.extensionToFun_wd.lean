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


theorem ExtensionOfMaxAdjoin.extensionToFun_wd (h : Module.Baer R Q) {y : N}
    (x : supExtensionOfMaxSingleton i f y) (a : (Module.Baer.extensionOfMax i f).domain)
    (r : R) (eq1 : ↑x = ↑a + r • y) :
    Module.Baer.ExtensionOfMaxAdjoin.extensionToFun i f h x =
      (Module.Baer.extensionOfMax i f).toLinearPMap a + Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo i f h y r := by
  obtain ⟨a, ha⟩ := a
  have eq2 :
    (Module.Baer.ExtensionOfMaxAdjoin.fst i x - a : N) = (r - Module.Baer.ExtensionOfMaxAdjoin.snd i x) • y := by
    change x = a + r • y at eq1
    rwa [Module.Baer.ExtensionOfMaxAdjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul]
      at eq1
  have eq3 :=
    Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_eq i f h (r - Module.Baer.ExtensionOfMaxAdjoin.snd i x)
      (by rw [← eq2]; exact Submodule.sub_mem _ (Module.Baer.ExtensionOfMaxAdjoin.fst i x).2 ha)
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3
  unfold Module.Baer.ExtensionOfMaxAdjoin.extensionToFun
  rw [eq3, ← add_assoc, ← (Module.Baer.extensionOfMax i f).toLinearPMap.map_add, AddMemClass.mk_add_mk]
  Module.Baer.congr
  ext
  dsimp
  rw [Subtype.coe_mk, add_sub, ← eq1]
  exact eq_sub_of_add_eq (Module.Baer.ExtensionOfMaxAdjoin.eqn i x).symm

