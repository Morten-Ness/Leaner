import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [Preorder β] [MulLeftStrictMono M] [MulRightStrictMono M] {f : β → M} {n : ℕ}

theorem StrictMono.pow_const (hf : StrictMono f) : ∀ {n : ℕ}, n ≠ 0 → StrictMono (f · ^ n)
  | 0, hn => (hn rfl).elim
  | 1, _ => by simpa
  | Nat.succ <| Nat.succ n, _ => by
    simpa only [pow_succ] using (hf.pow_const n.succ_ne_zero).mul' hf
