import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

variable (i f) [Fact <| Function.Injective i]

theorem extensionOfMax_is_max :
    ∀ (a : ExtensionOf i f), Module.Baer.extensionOfMax i f ≤ a → a = Module.Baer.extensionOfMax i f := fun _ ↦ (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
    ⟨Module.Baer.ExtensionOf.max hchain hnonempty, Module.Baer.ExtensionOf.le_max hchain hnonempty⟩).choose_spec.eq_of_ge

-- Auxiliary definition: Lean looks for an instance of `Max (Type u)` if we would write
-- `(x : (Module.Baer.extensionOfMax i f).domain ⊔ (Submodule.span R {y}))`, so we encapsulate the cast instead.
abbrev supExtensionOfMaxSingleton (y : N) : Submodule R N :=
  (Module.Baer.extensionOfMax i f).domain ⊔ (Submodule.span R {y})

