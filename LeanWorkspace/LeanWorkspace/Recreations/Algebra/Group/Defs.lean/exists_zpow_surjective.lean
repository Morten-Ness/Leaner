import Mathlib

variable {G : Type*}

theorem exists_zpow_surjective (G : Type*) [Pow G ℤ] [IsCyclic G] :
    ∃ g : G, Function.Surjective (g ^ · : ℤ → G) := IsCyclic.exists_zpow_surjective

