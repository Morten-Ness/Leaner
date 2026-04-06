FAIL
import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem pi_eq_bot_iff (S : ∀ i, Submonoid (M i)) :
    Submonoid.pi Set.univ S = (⊥ : Submonoid ((i : ι) → M i)) ↔ ∀ i, S i = ⊥ := by
  constructor
  · intro h i
    apply le_antisymm
    · intro x hx
      have hle : Submonoid.pi Set.univ S ≤ (⊥ : Submonoid ((i : ι) → M i)) := by
        simpa [h]
      have hx' : Function.update 1 i x ∈ Submonoid.pi Set.univ S := by
        intro j hj
        by_cases hji : j = i
        · subst hji
          simpa using hx
        · simp [Function.update, hji]
      have hxbot : Function.update 1 i x ∈ (⊥ : Submonoid ((i : ι) → M i)) := hle hx'
      have : x = 1 := by
        have := congrArg (fun f => f i) (show Function.update 1 i x = 1 from hxbot)
        simpa [Function.update] using this
      simpa [Submonoid.mem_bot, this]
    · intro x hx
      simpa [Submonoid.mem_bot] using hx
  · intro h
    apply le_antisymm
    · intro f hf
      rw [Submonoid.mem_bot]
      funext i
      have hfi : f i ∈ S i := hf i (by trivial)
      simpa [h i, Submonoid.mem_bot] using hfi
    · intro f hf
      intro i hi
      rw [h i]
      rw [Submonoid.mem_bot]
      exact congrArg (fun g => g i) hf
