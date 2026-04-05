import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem StrictMono.div_const {β : Type*} [Preorder β] {f : β → α} (hf : StrictMono f) {c : α}
    (hc : 0 < c) : StrictMono fun x => f x / c := by
  simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

-- see Note [lower instance priority]

