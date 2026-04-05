import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem coe_finsetInf {ι} (s : Finset ι) (p : ι → Submodule R M) :
    (↑(s.inf p) : Set M) = ⋂ i ∈ s, ↑(p i) := by
  letI := Classical.decEq ι
  refine s.induction_on ?_ fun i s _ ih ↦ ?_
  · simp
  · rw [Finset.inf_insert, Submodule.coe_inf, ih]
    simp

