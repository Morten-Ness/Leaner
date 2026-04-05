import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable {I : Type*} [DecidableEq I] {M : I → Type*}

variable [∀ i, CommMonoid (M i)]

theorem MonoidHom.functions_ext' [Finite I] (N : Type*) [CommMonoid N] (g h : (∀ i, M i) →* N)
    (H : ∀ i, g.comp (MonoidHom.mulSingle M i) = h.comp (MonoidHom.mulSingle M i)) : g = h := g.functions_ext N h fun i => DFunLike.congr_fun (H i)

