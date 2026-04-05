import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem ofMul_image_zpowers_eq_zmultiples_ofMul {x : G} :
    Additive.ofMul '' (Subgroup.zpowers x : Set G) = AddSubgroup.zmultiples (Additive.ofMul x) := by
  ext
  exact Set.mem_image_iff_of_inverse (congrFun rfl) (congrFun rfl)

