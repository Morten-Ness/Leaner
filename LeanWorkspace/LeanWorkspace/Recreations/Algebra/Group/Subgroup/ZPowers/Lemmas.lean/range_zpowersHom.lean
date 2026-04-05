import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem range_zpowersHom (g : G) : (zpowersHom G g).range = zpowers g := rfl

