import Mathlib

variable {α β : Type*}

variable [NonUnitalCommSemiring α]

theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y := dvd_add (hdx.mul_left a) (hdy.mul_left b)

