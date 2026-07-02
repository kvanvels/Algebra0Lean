import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Quot
import Mathlib.Order.RelClasses
import Mathlib.Tactic.ByContra
import Mathlib.Data.Set.Basic

/-!
# Chapter I: Preliminaries — Set theory and categories

Selected results from Aluffi, *Algebra: Chapter 0*, §I.1 (Naive set
theory) and §I.2 (Functions between sets).
-/

namespace Algebra0Lean.Prelims

section EquivalenceRelationsAndPartitions

variable {X : Type*}

/-- A partition of `X`: a set of nonempty subsets of `X`, every element
of which lies in exactly one of them. -/
def IsPartition (c : Set (Set X)) : Prop :=
  ∅ ∉ c ∧ ∀ a : X, ∃! s ∈ c, a ∈ s

/-- The set of equivalence classes of a setoid on `X`. -/
def setoidClasses (r : Setoid X) : Set (Set X) :=
  {s : Set X | ∃ y : X, s = {x : X | x ≈ y}}

/-- **Exercise I.1.2.** The equivalence classes of a setoid on `X` form
a partition of `X`. -/
theorem isPartition_setoidClasses (r : Setoid X) :
    IsPartition (setoidClasses r) := by
  constructor
  intro h0
  unfold setoidClasses at h0
  dsimp at h0
  rcases h0 with ⟨y,hy⟩
  let P : Set X := {x | x ≈ y}
  
  have h1 : P ⊆ ∅ := by sorry
  have h2 : y ∈ P := by
    unfold P
    show y ≈ y
    apply refl
  exact h1 h2
  intro y
  let P : Set X := {x | x ≈ y}
  use P
  apply And.intro
  dsimp
  apply And.intro
  unfold setoidClasses
  use y
  unfold P
  show y ≈ y
  apply refl
  intro Q ⟨hQ0,hQ1⟩
  unfold setoidClasses at hQ0
  rcases hQ0 with ⟨q,hQ0⟩
  
  apply subset_antisymm
  intro q hq
  have h1 : q ≈ y := by sorry
  unfold P
  exact h1
  intro p hp
  have h1 : p ≈ y := by sorry
  rw [hQ0] at hQ1
  rw [hQ0]
  unfold P at hp
  show p ≈ q
  clear hp
  have hy : y ≈ q := by sorry
  exact Setoid.trans h1 hy
  
  
  
  
  

end EquivalenceRelationsAndPartitions

section InjectiveSurjectiveInverses

variable {X Y : Type*}

/-- **Proposition I.2.4.** Assume `X` is nonempty, and let `f : X → Y`
be a function. Then `f` has a left-inverse if and only if it is
injective. -/
theorem hasLeftInverse_iff_injective [Nonempty X] (f : X → Y) :
    Function.HasLeftInverse f ↔ Function.Injective f := by
  sorry

/-- **Proposition I.2.4** (second part). `f` has a right-inverse if
and only if it is surjective. -/
theorem hasRightInverse_iff_surjective (f : X → Y) :
    Function.HasRightInverse f ↔ Function.Surjective f := by
  sorry

/-- **Corollary I.2.5.** A function is a bijection if and only if it
has a (two-sided) inverse. -/
theorem bijective_iff_hasInverse [Nonempty X] (f : X → Y) :
    Function.Bijective f ↔
      ∃ g : Y → X, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  sorry

end InjectiveSurjectiveInverses

section MonomorphismsAndEpimorphisms

universe u
variable {X Y : Type u}

/-- `f` is a monomorphism: it is left-cancellable when precomposed with
any function out of an arbitrary set `Z`. -/
def Monomorphic (f : X → Y) : Prop :=
  ∀ (Z : Type u) (g g' : Z → X), f ∘ g = f ∘ g' → g = g'

/-- `f` is an epimorphism: any function out of `Y` factors through `f`
after precomposing with some function into `X`. -/
def Epimorphic (f : X → Y) : Prop :=
  ∀ (Z : Type u) (g : Z → Y), ∃ h : Z → X, f ∘ h = g

/-- **Proposition I.2.3.** A function is injective if and only if it is
a monomorphism. -/
theorem injective_iff_monomorphic (f : X → Y) [Nonempty X] :
    Function.Injective f ↔ Monomorphic f := by
  apply Iff.intro
  intro h0 Z g0 g1 h01
  apply funext
  intro z
  have h1 := congr_fun h01 z
  

  exact @h0 (g0 z) (g1 z) h1  
  intro h0 a0 a1 h1
  specialize h0 X (fun x ↦ a0) (fun x ↦ a1) ?_
  funext θ
  exact h1
  have h2 : ∃ y : X, True := (exists_const X).mpr trivial
  rcases h2 with ⟨y,hy⟩
  
  have h1 := congr_fun h0  y
  exact h1
  
    


/-- **Exercise I.2.5.** A function is surjective if and only if it is
an epimorphism. -/
theorem epimorphic_iff_surjective (f : X → Y) :
    Epimorphic f ↔ Function.Surjective f := by
  apply Iff.intro
  intro h0 y
  unfold Epimorphic at h0
  specialize h0 Y id
  rcases h0 with ⟨finv,hfinv⟩
  use (finv y)
  
  rw [←@Function.comp_apply X Y Y f finv y,hfinv,id_eq]
  
  rintro h0 Z g

  have h1 := h0.hasRightInverse
  unfold Function.HasRightInverse at h1
  rcases h1 with ⟨finv,hfinv⟩
  clear h0
  use finv ∘ g

  unfold Function.RightInverse at hfinv
  unfold Function.LeftInverse at hfinv
  apply funext
  intro z
  rw [←Function.comp_assoc,Function.comp_apply]
  exact hfinv (g z)
  
  


end MonomorphismsAndEpimorphisms

section CanonicalDecomposition

variable {X Y : Type*}

/-- The equivalence relation on `X` induced by a function `f : X → Y`,
identifying `x`, `x'` whenever `f x = f x'`. -/
def kernelPairSetoid (f : X → Y) : Setoid X where
  r a b := f a = f b
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := by
      intro x y z h0 h1
      rwa [h0]
  }

/-- The canonical (surjective) projection `X ↠ X/∼` of
`Theorem I.2.8`. -/
def canonicalProjection (f : X → Y) : X → Quotient (kernelPairSetoid f) :=
  fun a ↦ ⟦a⟧

theorem canonicalProjection_surjective (f : X → Y) :
    (canonicalProjection f).Surjective := by
  intro p
  by_contra! h0
  unfold kernelPairSetoid at p
  unfold Quotient at p
  
  sorry
  


/-- The induced bijection `X/∼ ≅ image f` of `Theorem I.2.8`. -/
def canonicalBijection (f : X → Y) :
    Quotient (kernelPairSetoid f) → Set.range f := fun x ↦
  ⟨Quotient.lift f (fun _ _ h ↦ h) x, by
    rcases Quotient.exists_rep x with ⟨a, rfl⟩
    exact ⟨a, rfl⟩⟩

theorem canonicalBijection_bijective (f : X → Y) :
    (canonicalBijection f).Bijective := by
  apply And.intro
  intro y0
  sorry
  sorry

/-- The canonical (injective) inclusion `image f ↪ Y` of
`Theorem I.2.8`. -/
def canonicalInclusion (f : X → Y) : Set.range f → Y := fun x ↦ x.val

theorem canonicalInclusion_injective (f : X → Y) :
    (canonicalInclusion f).Injective := by
  intro ⟨y0,⟨x0,h0⟩⟩ ⟨y1,⟨x1,h1⟩ ⟩ h2  
  unfold canonicalInclusion at h2
  rcases h2 with ⟨h20,h21⟩
  rfl
    

/-- **Theorem I.2.8** (canonical decomposition of a function). Every
function factors as a surjection, followed by a bijection, followed by
an injection. -/
theorem canonicalDecomposition (f : X → Y) :
    f = canonicalInclusion f ∘ canonicalBijection f ∘ canonicalProjection f := by
  apply funext
  intro θ
  simp
  unfold canonicalProjection
  unfold canonicalBijection
  unfold canonicalInclusion  
  simp only [Quotient.lift_mk]
  

end CanonicalDecomposition

end Algebra0Lean.Prelims
