import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_assoc' [GCDMonoid α] (m n k : α) : Associated (lcm (lcm m n) k) (lcm m (lcm n k)) := associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

