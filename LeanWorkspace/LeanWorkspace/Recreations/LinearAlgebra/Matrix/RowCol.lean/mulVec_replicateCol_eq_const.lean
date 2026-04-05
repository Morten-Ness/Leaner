import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

theorem mulVec_replicateCol_eq_const [Fintype m] [NonUnitalNonAssocSemiring α] (v w : m → α) :
    v ᵥ* Matrix.replicateCol ι w = Function.const _ (v ⬝ᵥ w) := rfl

