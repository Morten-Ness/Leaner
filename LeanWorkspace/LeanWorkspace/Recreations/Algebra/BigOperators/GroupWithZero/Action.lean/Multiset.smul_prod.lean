import Mathlib

variable {M N γ : Type*}

theorem smul_prod [Monoid M] [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (s : Multiset N) (b : M) :
    b ^ card s • s.prod = (s.map (b • ·)).prod := Quot.induction_on s <| by simp [List.smul_prod]

