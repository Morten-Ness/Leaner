import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeInf T] [OrderTop T] (D : A → T)

theorem le_infDegree_mul [AddZeroClass A] [Add T] [AddLeftMono T] [AddRightMono T]
    (D : AddHom A T) (f g : R[A]) :
    f.infDegree D + g.infDegree D ≤ (f * g).infDegree D := AddMonoidAlgebra.le_inf_support_mul (fun {a b : A} => (map_add D a b).ge) _ _

