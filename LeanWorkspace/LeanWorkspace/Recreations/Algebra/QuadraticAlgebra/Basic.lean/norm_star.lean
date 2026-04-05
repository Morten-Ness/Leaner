import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_star (x : QuadraticAlgebra R a b) : (star x).norm = x.norm := by
  simp only [QuadraticAlgebra.norm, MonoidHom.coe_mk, OneHom.coe_mk, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, mul_neg, neg_mul, neg_neg,
    sub_left_inj]
  ring

