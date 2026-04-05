import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M := not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| Submodule.subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)

