import Mathlib

variable {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]

variable [Finite ι] [Infinite K]

theorem Module.Dual.exists_forall_ne_zero_of_forall_exists
    (f : ι → Dual K M) (h : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ x, ∀ i, f i x ≠ 0 := by
  let p i := LinearMap.ker (f i)
  replace h i : p i ≠ ⊤ := by specialize h i; aesop
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p h
  exact ⟨x, by simpa [p] using hx⟩

