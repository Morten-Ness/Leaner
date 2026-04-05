import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

theorem quasiIsoAt_ιTruncLE (n q : ℤ) (hq : q ≤ n) :
    QuasiIsoAt (K.ιTruncLE n) q := by
  obtain ⟨k, rfl⟩ := Int.le.dest hq
  exact HomologicalComplex.quasiIsoAt_ιTruncLE (j := k) _ _ (by simp)

