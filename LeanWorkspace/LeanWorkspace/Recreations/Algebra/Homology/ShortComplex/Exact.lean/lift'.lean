import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem lift' (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    ∃ (l : A ⟶ S.X₁), l ≫ S.f = k := ⟨hS.lift k hk, by simp⟩

