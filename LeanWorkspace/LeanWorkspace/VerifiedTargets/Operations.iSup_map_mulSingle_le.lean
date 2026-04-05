import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {ι : Type*} {M : ι → Type*} [∀ i, MulOneClass (M i)]

theorem iSup_map_mulSingle_le [DecidableEq ι] {I : Set ι} {S : ∀ i, Submonoid (M i)} :
    ⨆ i, Submonoid.map (MonoidHom.mulSingle M i) (S i) ≤ Submonoid.pi I S := iSup_le fun _ => Submonoid.map_le_iff_le_comap.mpr (Submonoid.le_comap_mulSingle_pi _)

