import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem Units.mulLeft_bijective _root_.Group (a : G) : Function.Bijective (a * ·) := (Equiv.mulLeft a).bijective

