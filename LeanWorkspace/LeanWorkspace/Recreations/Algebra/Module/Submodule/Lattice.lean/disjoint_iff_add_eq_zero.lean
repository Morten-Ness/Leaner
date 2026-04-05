import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem disjoint_iff_add_eq_zero {M R : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N₁ N₂ : Submodule R M} :
    Disjoint N₁ N₂ ↔ ∀ {x y : M}, x ∈ N₁ → y ∈ N₂ → x + y = 0 → x = 0 ∧ y = 0 := by
  simp only [← Submodule.mem_toAddSubgroup, ← AddSubgroup.disjoint_iff_add_eq_zero]
  aesop (add norm [Submodule.disjoint_def', AddSubgroup.disjoint_def'])

