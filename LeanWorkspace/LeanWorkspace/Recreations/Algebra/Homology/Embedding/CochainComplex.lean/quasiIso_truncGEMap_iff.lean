import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C]

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)

theorem quasiIso_truncGEMap_iff :
    QuasiIso (truncGEMap φ n) ↔ ∀ (i : ℤ) (_ : n ≤ i), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncGEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ rfl
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

