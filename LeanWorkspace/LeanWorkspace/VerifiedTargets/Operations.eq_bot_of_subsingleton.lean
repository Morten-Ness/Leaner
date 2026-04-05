import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem eq_bot_of_subsingleton [Subsingleton S] : S = ⊥ := by
  rw [Submonoid.eq_bot_iff_forall]
  intro y hy
  simpa using congr_arg ((↑) : S → M) <| Subsingleton.elim (⟨y, hy⟩ : S) 1

