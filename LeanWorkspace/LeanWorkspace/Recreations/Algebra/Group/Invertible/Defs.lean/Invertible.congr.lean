import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem Invertible.congr [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b := invertible_unique a b h

