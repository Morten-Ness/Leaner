import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem desc' (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    ∃ (l : S.X₃ ⟶ A), S.g ≫ l = k := ⟨hS.desc k hk, by simp⟩

