import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [DecidableEq α] {s t u : Finset α} {a : α}

theorem biUnion_op_smul_finset (s t : Finset α) : (t.biUnion fun a => op a • s) = s * t := biUnion_image_right

