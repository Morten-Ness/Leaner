import Mathlib

variable {R : Type*}

variable {p q : R}

theorem isStarNormal [Mul R] [Star R]
    (hp : IsStarProjection p) : IsStarNormal p := hp.isSelfAdjoint.isStarNormal

