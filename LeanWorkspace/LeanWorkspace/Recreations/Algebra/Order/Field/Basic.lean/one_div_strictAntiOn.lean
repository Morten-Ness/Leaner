import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem one_div_strictAntiOn : StrictAntiOn (fun x : α => 1 / x) (Set.Ioi 0) := fun _ x1 _ y1 xy => (one_div_lt_one_div (Set.mem_Ioi.mp y1) (Set.mem_Ioi.mp x1)).mpr xy

