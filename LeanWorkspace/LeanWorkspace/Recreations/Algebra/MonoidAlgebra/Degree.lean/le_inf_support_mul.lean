import Mathlib

variable {R R' A T B ι : Type*}

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

variable [Semiring R]

variable [Add A] [Add B] [Add T] [AddLeftMono B] [AddRightMono B]
  [AddLeftMono T] [AddRightMono T]

theorem le_inf_support_mul {degt : A → T} (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (f g : R[A]) :
    f.support.inf degt + g.support.inf degt ≤ (f * g).support.inf degt := AddMonoidAlgebra.sup_support_mul_le (B := Tᵒᵈ) degtm f g

