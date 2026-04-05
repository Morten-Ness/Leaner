import Mathlib

variable {R S M : Type*}

variable [AddCommGroup M]

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem AddSubgroup.coe_toIntSubmodule (S : AddSubgroup M) :
    (S.toIntSubmodule : Set M) = S := rfl

