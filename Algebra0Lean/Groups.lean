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

variable {G : Type*} (𝔾 : Group G)

/-- The group operation of `𝔾`, written infix as `g ∙ h`. -/
local infixl:70 " ∙ " => 𝔾.op

/-- `h` is an identity element for the group law of `𝔾`. -/
def IsIdentity (h : G) : Prop :=
  ∀ g : G, g ∙ h = g ∧ h ∙ g = g



/-- **Proposition II.1.2.** If `h` is an identity of `G`, then `h = e_G`. -/
theorem isIdentity_eq (h : G) (hh : IsIdentity 𝔾 h) : h = 𝔾.e := by
  have h1 := calc
   h = ( 𝔾.e ∙ h ) := by exact (𝔾.identity h).2.symm
    _ = 𝔾.e := by exact (hh 𝔾.e).1
  exact h1


/-- `h` is an inverse of `g` with respect to the group law of `𝔾`. -/
def IsInverse (g h : G) : Prop :=
  g ∙ h = 𝔾.e ∧ h ∙ g = 𝔾.e

/-- **Proposition II.1.3.** The inverse of `g` is unique: if `h₁`, `h₂`
are both inverses of `g` in `G`, then `h₁ = h₂`. -/
theorem isInverse_unique (g h1 h2 : G)
    (hh1 : IsInverse 𝔾 g h1) (hh2 : IsInverse 𝔾 g h2) : h1 = h2 := by
  have η1 := by calc
    h1 = h1 ∙ 𝔾.e := by sorry
     _ = h1 ∙ (g ∙ h2) := by sorry
     _ = (h1 ∙  g) ∙ h2 := by sorry
     _ = 𝔾.e ∙  h2 := by sorry
     _ = h2 := by sorry
  exact η1

end DefinitionOfGroup

section Cancellation

variable {G : Type*} (𝔾 : Group G)

local infixl:70 " ∙ " => 𝔾.op

/-- **Proposition II.1.4** (Cancellation). Let `G` be a group. Then for
all `a, g, h ∈ G`, `ga = ha ⟹ g = h` and `ag = ah ⟹ g = h`. -/
theorem cancel_right (a g h : G) (heq : g ∙ a = h ∙ a) : g = h := by
  have η1 := by calc
    g = g ∙ (a ∙ 𝔾.inv a) := by sorry
    _ = (g ∙ a) ∙ (𝔾.inv a) := by sorry
    _ = (h ∙ a) ∙ (𝔾.inv a) := by rw [heq]
    _ = h ∙ (a ∙ 𝔾.inv a) := by sorry
    _ = h := by sorry
  exact η1


theorem cancel_left (a g h : G) (heq : a ∙ g = a ∙ h) : g = h := by
  have η1 := by calc
   g = (𝔾.inv a ∙ a) ∙ g := by sorry
   _ = 𝔾.inv a ∙ (a ∙ g) := by sorry
   _ = 𝔾.inv a ∙ (a ∙ h) := by sorry
   _ = (𝔾.inv a ∙ a) ∙ h := by sorry
   _ = h := by sorry
  exact η1

end Cancellation

section CommutativeGroups

variable {G : Type*} (𝔾 : Group G)

local infixl:70 " ∙ " => 𝔾.op

/-- The group law of `𝔾` is commutative. -/
def IsCommutative : Prop :=
  ∀ g h : G, g ∙ h = h ∙ g

end CommutativeGroups

end Algebra0Lean.Groups
