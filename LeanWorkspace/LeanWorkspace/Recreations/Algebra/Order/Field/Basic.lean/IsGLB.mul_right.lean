import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem IsGLB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
    IsGLB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

