import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem component.of [DecidableEq ι] (i j : ι) (b : M j) :
    DirectSum.component R ι M i ((DirectSum.lof R ι M j) b) = if h : j = i then Eq.recOn h b else 0 := DFinsupp.single_apply

