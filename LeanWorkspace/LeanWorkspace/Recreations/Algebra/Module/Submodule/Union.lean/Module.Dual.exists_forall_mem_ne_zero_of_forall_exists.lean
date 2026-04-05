import Mathlib

variable {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]

variable [Finite ι] [Infinite K]

theorem Module.Dual.exists_forall_mem_ne_zero_of_forall_exists (p : Submodule K M)
    (f : ι → Dual K M) (h : ∀ i, ∃ x ∈ p, f i x ≠ 0) :
    ∃ x ∈ p, ∀ i, f i x ≠ 0 := by
  let f' (i : ι) : Dual K p := (f i).domRestrict p
  replace h (i : ι) : ∃ x : p, f' i x ≠ 0 := by obtain ⟨x, hxp, hx₀⟩ := h i; exact ⟨⟨x, hxp⟩, hx₀⟩
  obtain ⟨⟨x, hxp⟩, hx₀⟩ := exists_forall_ne_zero_of_forall_exists f' h
  exact ⟨x, hxp, hx₀⟩

