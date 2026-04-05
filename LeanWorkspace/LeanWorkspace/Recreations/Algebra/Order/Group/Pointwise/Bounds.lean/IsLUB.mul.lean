import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem IsLUB.mul (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB (s * t) (a * b) := isLUB_image2_of_isLUB_isLUB (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs ht

