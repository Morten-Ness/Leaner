import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

omit [IsStrictOrderedRing α] in
theorem Monotone.div_const {β : Type*} [Preorder β] {f : β → α} (hf : Monotone f) {c : α}
    (hc : 0 ≤ c) : Monotone fun x => f x / c := (monotone_div_right_of_nonneg hc).comp hf

