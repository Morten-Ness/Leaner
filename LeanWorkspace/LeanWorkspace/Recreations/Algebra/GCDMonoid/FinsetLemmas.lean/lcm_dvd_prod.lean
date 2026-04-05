import Mathlib

variable {ι α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_dvd_prod (s : Finset ι) (f : ι → α) : s.lcm f ∣ s.prod f := lcm_dvd fun _ ↦ dvd_prod_of_mem _

