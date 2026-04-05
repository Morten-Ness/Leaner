import Mathlib

variable {I : Type u}

variable {f : I → Type v}

theorem single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
    (r : α) (x : β) : single (M := fun _ => β) i (r • x) = r • single (M := fun _ => β) i x :=
  Pi.single_smul (f := fun _ => β) i r x

