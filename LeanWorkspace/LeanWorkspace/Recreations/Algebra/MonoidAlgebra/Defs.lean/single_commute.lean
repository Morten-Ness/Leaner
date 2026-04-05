import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem single_commute (hm : ∀ m', Commute m m') (hr : ∀ r', Commute r r') (x : R[M]) :
    Commute (single m r) x := by
  have : AddMonoidHom.mulLeft (single m r) = AddMonoidHom.mulRight (single m r) := by
    ext m' r' : 2; exact MonoidAlgebra.single_commute_single (hm m') (hr r')
  exact congr($this x)

