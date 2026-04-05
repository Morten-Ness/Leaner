import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable {x y : α}

theorem isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x := isRelPrime_comm.trans isRelPrime_zero_left

