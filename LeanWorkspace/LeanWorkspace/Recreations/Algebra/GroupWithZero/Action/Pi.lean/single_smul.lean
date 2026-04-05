import Mathlib

variable {I : Type u}

variable {f : I → Type v}

theorem single_smul {α} [Monoid α] [∀ i, AddMonoid <| f i] [∀ i, DistribMulAction α <| f i]
    [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x) = r • single i x := single_op (fun i : I => (r • · : f i → f i)) (fun _ => smul_zero _) _ _

