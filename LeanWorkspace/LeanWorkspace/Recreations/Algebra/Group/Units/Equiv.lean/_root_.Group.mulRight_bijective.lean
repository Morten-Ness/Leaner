import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem Units.mulRight_bijective _root_.Group (a : G) : Function.Bijective (· * a) := (Equiv.mulRight a).bijective

