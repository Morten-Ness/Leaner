import Mathlib

variable {I : Type u}

variable {f : I → Type v}

theorem update_star [∀ i, Star (f i)] [DecidableEq I] (h : ∀ i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) := funext fun j => (apply_update (fun _ => star) h i a j).symm

