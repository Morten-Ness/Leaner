import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

theorem range_eq_top (e : G ≃* G') : (e : G →* G').range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective

