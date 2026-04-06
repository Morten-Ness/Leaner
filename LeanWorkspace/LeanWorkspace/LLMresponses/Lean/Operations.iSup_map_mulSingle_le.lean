import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem iSup_map_mulSingle_le [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} :
    ⨆ i, Submonoid.map (MonoidHom.mulSingle M i) (S i) ≤ Submonoid.pi I S := by
  classical
  refine iSup_le ?_
  intro i
  refine Submonoid.map_le_iff_le_comap.2 ?_
  intro x hx j hj
  by_cases h : j = i
  · subst h
    simpa using hx
  · simp [MonoidHom.mulSingle, h]
