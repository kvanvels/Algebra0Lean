import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Find
import Mathlib.SetTheory.Cardinal.Finite

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

/-- The group operation of `𝔾`, written infix as `g ⋆ h`. -/
local infixl:70 " ⋆ " => 𝔾.op

/-- `h` is an identity element for the group law of `𝔾`. -/
def IsIdentity (h : G) : Prop :=
  ∀ g : G, g ⋆ h = g ∧ h ⋆ g = g



/-- **Proposition II.1.2.** If `h` is an identity of `G`, then `h = e_G`. -/
theorem isIdentity_eq (h : G) (hh : IsIdentity 𝔾 h) : h = 𝔾.e := by
  have h1 := calc
   h = ( 𝔾.e ⋆ h ) := by exact (𝔾.identity h).2.symm
    _ = 𝔾.e := by exact (hh 𝔾.e).1
  exact h1


/-- `h` is an inverse of `g` with respect to the group law of `𝔾`. -/
def IsInverse (g h : G) : Prop :=
  g ⋆ h = 𝔾.e ∧ h ⋆ g = 𝔾.e

/-- **Proposition II.1.3.** The inverse of `g` is unique: if `h₁`, `h₂`
are both inverses of `g` in `G`, then `h₁ = h₂`. -/
theorem isInverse_unique (g h1 h2 : G)
    (hh1 : IsInverse 𝔾 g h1) (hh2 : IsInverse 𝔾 g h2) : h1 = h2 := by
  have η1 := by calc
    h1 = h1 ⋆ 𝔾.e := by exact (𝔾.identity h1).1.symm
     _ = h1 ⋆ (g ⋆ h2) := by rw [hh2.1]
     _ = (h1 ⋆  g) ⋆ h2 := by rw [𝔾.assoc]
     _ = 𝔾.e ⋆  h2 := by rw [hh1.2]
     _ = h2 := by exact (𝔾.identity h2).2     
  exact η1

end DefinitionOfGroup

section Cancellation

variable {G : Type*} (𝔾 : Group G)

local infixl:70 " ⋆ " => 𝔾.op

/-- **Proposition II.1.4** (Cancellation). Let `G` be a group. Then for
all `a, g, h ∈ G`, `ga = ha ⟹ g = h` and `ag = ah ⟹ g = h`. -/
theorem cancel_right (a g h : G) (heq : g ⋆ a = h ⋆ a) : g = h := by calc
    g = g ⋆ 𝔾.e := by exact (𝔾.identity g).1.symm
    _ = g ⋆ (a ⋆ 𝔾.inv a) := by rw [(𝔾.inverse a).1.symm]
    _ = (g ⋆ a) ⋆ (𝔾.inv a) := by rw [𝔾.assoc]
    _ = (h ⋆ a) ⋆ (𝔾.inv a) := by rw [heq]
    _ = h ⋆ (a ⋆ 𝔾.inv a) := by rw [𝔾.assoc]
    _ = h ⋆ 𝔾.e := by rw [(𝔾.inverse a).1]
    _ = h := by exact (𝔾.identity h).1

theorem cancel_left (a g h : G) (heq : a ⋆ g = a ⋆ h) : g = h := by
  have η1 := by calc
   g = 𝔾.e ⋆ g := by exact (𝔾.identity g).2.symm
   _ = (𝔾.inv a ⋆ a) ⋆ g := by rw [(𝔾.inverse a).2]
   _ = 𝔾.inv a ⋆ (a ⋆ g) := by rw [𝔾.assoc]
   _ = 𝔾.inv a ⋆ (a ⋆ h) := by rw [heq]
   _ = (𝔾.inv a ⋆ a) ⋆ h := by rw [𝔾.assoc]
   _ = 𝔾.e ⋆ h := by rw [(𝔾.inverse a).2]
   _ = h := by exact (𝔾.identity h).2
  exact η1

end Cancellation

section CommutativeGroups

variable {G : Type*} (𝔾 : Group G)

local infixl:70 " ⋆ " => 𝔾.op

/-- The group law of `𝔾` is commutative. -/
def IsCommutative : Prop :=
  ∀ g h : G, g ⋆ h = h ⋆ g

end CommutativeGroups

section Order

variable {G : Type*}

/-- The `n`-th power of `g` under the group law of `𝔾`. -/
def gpow (𝔾 : Group G) (g : G) : ℕ → G
  | 0 => 𝔾.e
  | n + 1 => 𝔾.op (gpow 𝔾 g n) g

/-- The `n`-th power of `g`, for `n : ℤ`, using `𝔾.inv` for negative
exponents. -/
def gzpow (𝔾 : Group G) (g : G) : ℤ → G
  | Int.ofNat n => gpow 𝔾 g n
  | Int.negSucc n => 𝔾.inv (gpow 𝔾 g (n + 1))

/-- `g` has finite order if `g^n = e` for some positive `n`. -/
def HasFiniteOrder (𝔾 : Group G) (g : G) : Prop :=
  ∃ n : ℕ, 0 < n ∧ gpow 𝔾 g n = 𝔾.e

/-- **Definition II.1.5.** The order of `g`: the least positive `n`
with `g^n = e`, or `0` if `g` has infinite order (Aluffi's `|g| = ∞`). -/
noncomputable def order (𝔾 : Group G) (g : G) : ℕ := by
  classical exact if h : HasFiniteOrder 𝔾 g then Nat.find h else 0

/-- **Lemma II.1.5.** If `g^n = e` for some positive integer `n`, then
`|g|` is a divisor of `n`. -/
theorem order_dvd_of_pow_eq_e (𝔾 : Group G) (g : G) (n : ℕ) (hn : 0 < n)
    (he : gpow 𝔾 g n = 𝔾.e) : order 𝔾 g ∣ n := by
  sorry

/-- **Corollary II.1.6.** Let `g` be an element of finite order, and
let `N : ℤ`. Then `g^N = e ↔ N` is a multiple of `|g|`. -/
theorem gzpow_eq_e_iff_dvd_order (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g)
    (N : ℤ) : gzpow 𝔾 g N = 𝔾.e ↔ (order 𝔾 g : ℤ) ∣ N := by
  sorry

/-- **Definition.** If `G` is finite as a set, its order `|G|` is the
number of its elements; `0` if `G` is infinite (Aluffi's `|G| = ∞`). -/
noncomputable def groupOrder : ℕ := Nat.card G

/-- **Proposition II.1.7.** Let `g` be an element of finite order.
Then `g^m` has finite order for all `m ≥ 0`, and
`|g^m| = lcm(m, |g|) / m = |g| / gcd(m, |g|)`. -/
theorem order_gpow (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g) (m : ℕ) :
    order 𝔾 (gpow 𝔾 g m) = Nat.lcm m (order 𝔾 g) / m := by
  sorry

/-- **Proposition II.1.8.** If `g` and `h` commute, then `|gh|` divides
`lcm(|g|, |h|)`. -/
theorem order_op_dvd_lcm (𝔾 : Group G) (g h : G) (hcomm : 𝔾.op g h = 𝔾.op h g) :
    order 𝔾 (𝔾.op g h) ∣ Nat.lcm (order 𝔾 g) (order 𝔾 h) := by
  sorry

end Order

end Algebra0Lean.Groups
