import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C]

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)

theorem quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ n) ↔ ∀ (i : ℤ) (_ : i ≤ n), QuasiIsoAt φ i := by
  rw [HomologicalComplex.quasiIso_truncLEMap_iff]
  constructor
  · intro h i hi
    obtain ⟨k, rfl⟩ := Int.le.dest hi
    exact h k _ (by dsimp; lia)
  · rintro h i i' rfl
    exact h _ (by dsimp; lia)

