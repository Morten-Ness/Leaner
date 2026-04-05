import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem sub_mem_sup {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M']
    {S T : Submodule R' M'} {s t : M'} (hs : s ∈ S) (ht : t ∈ T) : s - t ∈ S ⊔ T := by
  rw [sub_eq_add_neg]
  exact Submodule.add_mem_sup hs (neg_mem ht)

