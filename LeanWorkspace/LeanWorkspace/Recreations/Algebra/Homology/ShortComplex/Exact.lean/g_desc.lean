import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem g_desc (hS : S.Exact) {A : C} (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [Epi S.g] :
    S.g ≫ hS.desc k hk = k := Cofork.IsColimit.π_desc (hS.gIsCokernel)

