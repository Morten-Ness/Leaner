import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem lift_f (hS : S.Exact) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [Mono S.f] :
    hS.lift k hk ≫ S.f = k := Fork.IsLimit.lift_ι _

