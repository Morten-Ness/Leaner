import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

theorem chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)}
    (hchain : IsChain (· ≤ ·) c) :
    IsChain (· ≤ ·) <| (fun x : ExtensionOf i f => x.toLinearPMap) '' c := by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ ne
  exact hchain a_mem b_mem (ne_of_apply_ne _ ne)

