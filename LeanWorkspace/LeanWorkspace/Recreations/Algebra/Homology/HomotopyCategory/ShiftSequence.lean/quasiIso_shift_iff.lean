import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable [CategoryWithHomology C]

theorem quasiIso_shift_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    QuasiIso (φ⟦n⟧') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, fun i ↦ CochainComplex.quasiIsoAt_shift_iff φ n i _ rfl]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by lia⟩
    exact h i
  · intro h i
    exact h (n + i)

