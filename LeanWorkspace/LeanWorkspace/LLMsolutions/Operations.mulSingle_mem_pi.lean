import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem mulSingle_mem_pi [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} (i : ι) (x : M i) :
    Pi.mulSingle i x ∈ Submonoid.pi I S ↔ i ∈ I → x ∈ S i := by
  constructor
  · intro hx hi
    simpa [Submonoid.pi, Set.mem_setOf_eq] using hx i hi
  · intro hx j hj
    by_cases hji : j = i
    · subst hji
      simpa [Pi.mulSingle] using hx hj
    · simp [Pi.mulSingle, hji]
