import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem disjoint_def' {p p' : Submodule R M} :
    Disjoint p p' ↔ ∀ x ∈ p, ∀ y ∈ p', x = y → x = (0 : M) := Submodule.disjoint_def.trans
    ⟨fun h x hx _ hy hxy ↦ h x hx <| hxy.symm ▸ hy, fun h x hx hx' ↦ h _ hx x hx' rfl⟩

