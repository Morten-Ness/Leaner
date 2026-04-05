import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι, f.comp (DirectSum.of _ i) = g.comp (DirectSum.of _ i)) : f = g := DirectSum.addHom_ext fun i => DFunLike.congr_fun <| H i

