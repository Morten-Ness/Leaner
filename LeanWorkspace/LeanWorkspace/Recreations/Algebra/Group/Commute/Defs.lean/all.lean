import Mathlib

variable {G M S : Type*}

theorem all [CommMagma S] (a b : S) : Commute a b := mul_comm a b

