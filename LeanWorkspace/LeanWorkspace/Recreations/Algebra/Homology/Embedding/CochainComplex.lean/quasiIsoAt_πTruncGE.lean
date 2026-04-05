import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

theorem quasiIsoAt_πTruncGE (n q : ℤ) (hq : n ≤ q) :
    QuasiIsoAt (K.πTruncGE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_πTruncGE (j := k) _ _ (by simp)

