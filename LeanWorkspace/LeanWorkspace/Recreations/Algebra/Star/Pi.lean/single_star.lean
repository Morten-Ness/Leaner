import Mathlib

variable {I : Type u}

variable {f : I → Type v}

theorem single_star [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) := single_op (fun i => @star (f i) _) (fun _ => star_zero _) i a

