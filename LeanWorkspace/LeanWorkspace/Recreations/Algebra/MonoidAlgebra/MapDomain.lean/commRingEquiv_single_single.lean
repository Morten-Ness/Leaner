import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

set_option backward.isDefEq.respectTransparency false in
theorem commRingEquiv_single_single (m : M) (n : N) (r : R) :
    MonoidAlgebra.commRingEquiv (single m <| single n r) = single n (single m r) := by
  simp [MonoidAlgebra.commRingEquiv, MonoidAlgebra, curryRingEquiv, curryAddEquiv, MonoidAlgebra.mapDomainRingEquiv,
    MonoidAlgebra.mapDomainRingHom, EquivLike.toEquiv]

