import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

theorem ExtensionOf.ext {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq : ∀ ⦃x : N⦄ ⦃ha : x ∈ a.domain⦄ ⦃hb : x ∈ b.domain⦄,
      a.toLinearPMap ⟨x, ha⟩ = b.toLinearPMap ⟨x, hb⟩) :
    a = b := by
  rcases a with ⟨a, a_le, e1⟩
  Module.Baer.congr
  exact LinearPMap.ext domain_eq to_fun_eq

