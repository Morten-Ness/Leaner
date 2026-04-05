import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem Exact.isIso_map' {C : Type*} [Category* C] [Preadditive C]
    [Balanced C] {n : ℕ} {S : CategoryTheory.ComposableArrows C n} (hS : S.Exact) (k : ℕ) (hk : k + 3 ≤ n)
    (h₀ : S.map' k (k + 1) = 0) (h₁ : S.map' (k + 2) (k + 3) = 0) :
    IsIso (S.map' (k + 1) (k + 2)) := by
  have := (hS.exact k).mono_g h₀
  have := (hS.exact (k + 1)).epi_f h₁
  apply isIso_of_mono_of_epi

