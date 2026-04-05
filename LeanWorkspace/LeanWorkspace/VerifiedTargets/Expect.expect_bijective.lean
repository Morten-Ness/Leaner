import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_bijective (e : ι → κ) (he : Function.Bijective e) (f : ι → M) (g : κ → M)
    (h : ∀ i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i := Finset.expect_nbij e (fun _ _ ↦ Finset.mem_univ _) (fun i _ ↦ h i) he.injective.injOn <| by
    simpa using he.surjective

