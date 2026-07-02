import Mathlib

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
  sorry

end EquivalenceRelationsAndPartitions

section MonomorphismsAndEpimorphisms

variable {X Y : Type*}

/-- `f` is a monomorphism: it is left-cancellable when precomposed with
any function out of an arbitrary set `Z`. -/
def Monomorphic (f : X → Y) : Prop :=
  ∀ (Z : Type) (g g' : Z → X), f ∘ g = f ∘ g' → g = g'

/-- `f` is an epimorphism: any function out of `Y` factors through `f`
after precomposing with some function into `X`. -/
def Epimorphic (f : X → Y) : Prop :=
  ∀ (Z : Type) (g : Z → Y), ∃ h : Z → X, f ∘ h = g

/-- **Proposition I.2.3.** A function is injective if and only if it is
a monomorphism. -/
theorem injective_iff_monomorphic (f : X → Y) :
    Function.Injective f ↔ Monomorphic f := by
  sorry

/-- **Exercise I.2.5.** A function is surjective if and only if it is
an epimorphism. -/
theorem epimorphic_iff_surjective (f : X → Y) :
    Epimorphic f ↔ Function.Surjective f := by
  sorry

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
  sorry

/-- The induced bijection `X/∼ ≅ image f` of `Theorem I.2.8`. -/
def canonicalBijection (f : X → Y) :
    Quotient (kernelPairSetoid f) → Set.range f := fun x ↦
  ⟨Quotient.lift f (fun _ _ h ↦ h) x, by
    rcases Quotient.exists_rep x with ⟨a, rfl⟩
    exact ⟨a, rfl⟩⟩

theorem canonicalBijection_bijective (f : X → Y) :
    (canonicalBijection f).Bijective := by
  sorry

/-- The canonical (injective) inclusion `image f ↪ Y` of
`Theorem I.2.8`. -/
def canonicalInclusion (f : X → Y) : Set.range f → Y := fun x ↦ x.val

theorem canonicalInclusion_injective (f : X → Y) :
    (canonicalInclusion f).Injective := by
  sorry

/-- **Theorem I.2.8** (canonical decomposition of a function). Every
function factors as a surjection, followed by a bijection, followed by
an injection. -/
theorem canonicalDecomposition (f : X → Y) :
    f = canonicalInclusion f ∘ canonicalBijection f ∘ canonicalProjection f := by
  sorry

end CanonicalDecomposition

end Algebra0Lean.Prelims
