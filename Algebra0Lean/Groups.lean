import Mathlib

/-!
# Chapter II: Groups, first encounter

Selected results from Aluffi, *Algebra: Chapter 0*, §II.1 (Definition
of group).

This chapter defines its own `Group` structure from scratch, mirroring
the book's definition, rather than using Mathlib's `Group` typeclass —
so that the basic exercises (uniqueness of identity/inverse,
cancellation, ...) are genuine proof obligations. Later chapters
transition to Mathlib's `Group`.
-/

namespace Algebra0Lean.Groups

section DefinitionOfGroup

/-- **Definition II.1.1.** A group: a (nonempty, by virtue of `e`) type
`G` with an associative binary operation `op`, an identity `e` for
`op`, and inverses for every element. -/
structure Group (G : Type*) where
  op : G → G → G
  assoc : ∀ g h k : G, op (op g h) k = op g (op h k)
  e : G
  identity : ∀ g : G, op g e = g ∧ op e g = g
  inv : G → G
  inverse : ∀ g : G, op g (inv g) = e ∧ op (inv g) g = e

variable {G : Type*}

/-- `h` is an identity element for the group law of `𝔾`. -/
def IsIdentity (𝔾 : Group G) (h : G) : Prop :=
  ∀ g : G, 𝔾.op g h = g ∧ 𝔾.op h g = g

/-- **Proposition II.1.2.** If `h` is an identity of `G`, then `h = e_G`. -/
theorem isIdentity_eq (𝔾 : Group G) (h : G) (hh : IsIdentity 𝔾 h) :
    h = 𝔾.e := by
  sorry

/-- `h` is an inverse of `g` with respect to the group law of `𝔾`. -/
def IsInverse (𝔾 : Group G) (g h : G) : Prop :=
  𝔾.op g h = 𝔾.e ∧ 𝔾.op h g = 𝔾.e

/-- **Proposition II.1.3.** The inverse of `g` is unique: if `h₁`, `h₂`
are both inverses of `g` in `G`, then `h₁ = h₂`. -/
theorem isInverse_unique (𝔾 : Group G) (g h1 h2 : G)
    (hh1 : IsInverse 𝔾 g h1) (hh2 : IsInverse 𝔾 g h2) : h1 = h2 := by
  sorry

end DefinitionOfGroup

section Cancellation

variable {G : Type*}

/-- **Proposition II.1.4** (Cancellation). Let `G` be a group. Then for
all `a, g, h ∈ G`, `ga = ha ⟹ g = h` and `ag = ah ⟹ g = h`. -/
theorem cancel_right (𝔾 : Group G) (a g h : G)
    (heq : 𝔾.op g a = 𝔾.op h a) : g = h := by
  sorry

theorem cancel_left (𝔾 : Group G) (a g h : G)
    (heq : 𝔾.op a g = 𝔾.op a h) : g = h := by
  sorry

end Cancellation

section CommutativeGroups

variable {G : Type*}

/-- The group law of `𝔾` is commutative. -/
def IsCommutative (𝔾 : Group G) : Prop :=
  ∀ g h : G, 𝔾.op g h = 𝔾.op h g

end CommutativeGroups

end Algebra0Lean.Groups
