/- Auto-generated from `Algebra0Lean/Groups.lean` by `scripts/mk_exercises.py`.
   Do not edit by hand: fill in the `sorry`s in your own copy, and
   compare with `Algebra0Lean/Groups.lean` for the solutions. -/

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

namespace Exercises.Groups

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
  sorry

/-- `h` is an inverse of `g` with respect to the group law of `𝔾`. -/
def IsInverse (g h : G) : Prop :=
  g ⋆ h = 𝔾.e ∧ h ⋆ g = 𝔾.e

/-- **Proposition II.1.3.** The inverse of `g` is unique: if `h₁`, `h₂`
are both inverses of `g` in `G`, then `h₁ = h₂`. -/
theorem isInverse_unique (g h1 h2 : G)
    (hh1 : IsInverse 𝔾 g h1) (hh2 : IsInverse 𝔾 g h2) : h1 = h2 := by
  sorry

end DefinitionOfGroup

section Cancellation

variable {G : Type*} (𝔾 : Group G)

local infixl:70 " ⋆ " => 𝔾.op

/-- **Proposition II.1.4** (Cancellation). Let `G` be a group. Then for
all `a, g, h ∈ G`, `ga = ha ⟹ g = h` and `ag = ah ⟹ g = h`. -/
theorem cancel_right (a g h : G) (heq : g ⋆ a = h ⋆ a) : g = h :=
  sorry

theorem cancel_left (a g h : G) (heq : a ⋆ g = a ⋆ h) : g = h := by
  sorry

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

/-- Powers add: `g^(a+b) = g^a ⋆ g^b`. -/
theorem gpow_add (𝔾 : Group G) (g : G) (a b : ℕ) :
    gpow 𝔾 g (a + b) = 𝔾.op (gpow 𝔾 g a) (gpow 𝔾 g b) := by
  sorry

/-- Powers multiply: `g^(ab) = (g^a)^b`. -/
theorem gpow_mul (𝔾 : Group G) (g : G) (a b : ℕ) :
    gpow 𝔾 g (a * b) = gpow 𝔾 (gpow 𝔾 g a) b := by
  sorry

/-- Every power of the identity is the identity. -/
theorem gpow_e (𝔾 : Group G) (n : ℕ) : gpow 𝔾 𝔾.e n = 𝔾.e := by
  sorry

/-- If `h` commutes with `g`, it commutes with every power of `g`. -/
theorem gpow_op_comm (𝔾 : Group G) {g h : G} (hc : 𝔾.op g h = 𝔾.op h g) (n : ℕ) :
    𝔾.op (gpow 𝔾 g n) h = 𝔾.op h (gpow 𝔾 g n) := by
  sorry

/-- For commuting `g`, `h`, powers distribute: `(gh)^n = g^n ⋆ h^n`. -/
theorem gpow_op_of_comm (𝔾 : Group G) {g h : G} (hc : 𝔾.op g h = 𝔾.op h g) (n : ℕ) :
    gpow 𝔾 (𝔾.op g h) n = 𝔾.op (gpow 𝔾 g n) (gpow 𝔾 h n) := by
  sorry

/-- The identity is its own inverse. -/
theorem inv_e (𝔾 : Group G) : 𝔾.inv 𝔾.e = 𝔾.e :=
  sorry

/-- `g⁻¹ = e` if and only if `g = e`. -/
theorem inv_eq_e_iff (𝔾 : Group G) (x : G) : 𝔾.inv x = 𝔾.e ↔ x = 𝔾.e := by
  sorry

/-- `g` has finite order if `g^n = e` for some positive `n`. -/
def HasFiniteOrder (𝔾 : Group G) (g : G) : Prop :=
  ∃ n : ℕ, 0 < n ∧ gpow 𝔾 g n = 𝔾.e

/-- **Definition II.1.5.** The order of `g`: the least positive `n`
with `g^n = e`, or `0` if `g` has infinite order (Aluffi's `|g| = ∞`). -/
noncomputable def order (𝔾 : Group G) (g : G) : ℕ := by
  classical exact if h : HasFiniteOrder 𝔾 g then Nat.find h else 0

/-- An element of finite order has positive order. -/
theorem order_pos (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g) :
    0 < order 𝔾 g := by
  sorry

/-- `g^|g| = e` for an element of finite order. -/
theorem gpow_order (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g) :
    gpow 𝔾 g (order 𝔾 g) = 𝔾.e := by
  sorry

/-- Minimality of the order: no smaller positive power of `g` is `e`. -/
theorem gpow_ne_e_of_lt_order (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g)
    {m : ℕ} (hm : 0 < m) (hlt : m < order 𝔾 g) : gpow 𝔾 g m ≠ 𝔾.e := by
  sorry

/-- An element of infinite order has order `0` (Aluffi's `|g| = ∞`). -/
theorem order_eq_zero_of_infinite (𝔾 : Group G) (g : G)
    (hf : ¬HasFiniteOrder 𝔾 g) : order 𝔾 g = 0 := by
  sorry

/-- An element of positive order has finite order. -/
theorem hasFiniteOrder_of_order_pos (𝔾 : Group G) (g : G)
    (h : 0 < order 𝔾 g) : HasFiniteOrder 𝔾 g := by
  sorry

/-- **Lemma II.1.5.** If `g^n = e` for some positive integer `n`, then
`|g|` is a divisor of `n`. -/
theorem order_dvd_of_pow_eq_e (𝔾 : Group G) (g : G) (n : ℕ) (hn : 0 < n)
    (he : gpow 𝔾 g n = 𝔾.e) : order 𝔾 g ∣ n := by
  sorry

/-- Restatement of Lemma II.1.5 as an equivalence, for natural exponents:
`g^n = e` if and only if `|g|` divides `n`. -/
theorem gpow_eq_e_iff_order_dvd (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g)
    (n : ℕ) : gpow 𝔾 g n = 𝔾.e ↔ order 𝔾 g ∣ n := by
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
`|g^m| = lcm(m, |g|) / m = |g| / gcd(m, |g|)`.

The `lcm` form requires `0 < m`: for `m = 0` we have `|g^0| = |e| = 1`
while `lcm(0, |g|) / 0 = 0` in `ℕ` (Aluffi's second expression
`|g| / gcd(m, |g|)` does cover `m = 0`). -/
theorem order_gpow (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g) (m : ℕ)
    (hm : 0 < m) :
    order 𝔾 (gpow 𝔾 g m) = Nat.lcm m (order 𝔾 g) / m := by
  sorry

/-- **Proposition II.1.8.** If `g` and `h` commute, then `|gh|` divides
`lcm(|g|, |h|)`. -/
theorem order_op_dvd_lcm (𝔾 : Group G) (g h : G) (hcomm : 𝔾.op g h = 𝔾.op h g) :
    order 𝔾 (𝔾.op g h) ∣ Nat.lcm (order 𝔾 g) (order 𝔾 h) := by
  sorry

end Order

end Exercises.Groups
