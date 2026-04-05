import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

theorem ExtensionOf.le_max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) (a : ExtensionOf i f) (ha : a ∈ c) :
    a ≤ Module.Baer.ExtensionOf.max hchain hnonempty := LinearPMap.le_sSup (IsChain.directedOn <| Module.Baer.chain_linearPMap_of_chain_extensionOf hchain) <|
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩

