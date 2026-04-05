import Mathlib

variable {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]

variable [Finite ι] [Infinite K]

theorem Submodule.exists_forall_notMem_of_forall_ne_top (p : ι → Submodule K M) (h : ∀ i, p i ≠ ⊤) :
    ∃ x, ∀ i, x ∉ p i := by
  let _i : Fintype ι := Fintype.ofFinite ι
  suffices ⋃ i, (p i : Set M) ⊂ Set.univ by simpa [ssubset_univ_iff, iUnion_eq_univ_iff] using this
  simpa using iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ p h (by simp)

