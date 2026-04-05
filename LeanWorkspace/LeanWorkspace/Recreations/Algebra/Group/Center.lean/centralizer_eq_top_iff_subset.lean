import Mathlib

variable {M : Type*} {S T : Set M}

variable [Semigroup M] {a b : M}

theorem centralizer_eq_top_iff_subset : Set.centralizer S = Set.univ ↔ S ⊆ Set.center M := eq_top_iff.trans <| ⟨
    fun h _ hx ↦ Semigroup.mem_center_iff.mpr fun _ ↦ by rw [h trivial _ hx],
    fun h _ _ _ hm ↦ (h hm).comm _⟩

