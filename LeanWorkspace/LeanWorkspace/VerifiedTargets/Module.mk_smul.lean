import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

theorem mk_smul (s : Finset ι) (c : R) (x) : DirectSum.mk M s (c • x) = c • DirectSum.mk M s x := (DirectSum.lmk R ι M s).map_smul c x

