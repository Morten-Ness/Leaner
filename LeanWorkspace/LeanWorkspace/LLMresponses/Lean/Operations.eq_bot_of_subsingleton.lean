import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem eq_bot_of_subsingleton [Subsingleton S] : S = ⊥ := by
  ext x
  constructor
  · intro hx
    change x = 1
    have h : (⟨x, hx⟩ : S) = 1 := Subsingleton.elim _ _
    exact Subtype.ext_iff.mp h
  · intro hx
    rw [Submonoid.mem_bot] at hx
    rw [hx]
    exact S.one_mem
