import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Analysis.Real.Cardinality

/-! The bounded-range presheaf as a presheaf of commutative rings.

Mathlib's sheaf condition for `CommRingCat`-valued presheaves rejects it, although every
compatible family over a cover with at most continuum many members glues uniquely. The
Isabelle development shows that the AFP predicate `sheaf_of_rings` accepts the same presheaf.

The last theorem records Mathlib's proof of Hartshorne's Proposition II.1.1, which the
Isabelle theorem `stalkwise_iso_not_iso` shows to be false for the AFP predicate. -/

open CategoryTheory Opposite TopologicalSpace TopCat Cardinal

noncomputable section
namespace SchemesAudit

/-- A pointwise binary operation on two functions with at most continuum many values
has at most continuum many values. -/
lemma mk_range_map₂_le {U A : Type} (op : A → A → A) {f g : U → A}
    (hf : #(Set.range f) ≤ 𝔠) (hg : #(Set.range g) ≤ 𝔠) :
    #(Set.range fun x => op (f x) (g x)) ≤ 𝔠 := calc
  _ ≤ #(Set.range fun p : Set.range f × Set.range g => op p.1 p.2) :=
    Cardinal.mk_le_mk_of_subset (by
      rintro _ ⟨x, rfl⟩; exact ⟨(⟨f x, x, rfl⟩, ⟨g x, x, rfl⟩), rfl⟩)
  _ ≤ #(Set.range f × Set.range g) := Cardinal.mk_range_le
  _ = #(Set.range f) * #(Set.range g) := (Cardinal.mul_def _ _).symm
  _ ≤ 𝔠 * 𝔠 := mul_le_mul' hf hg
  _ = 𝔠 := Cardinal.continuum_mul_self

/-- A constant function has at most continuum many values. -/
lemma mk_range_const_le {U A : Type} (a : A) : #(Set.range fun _ : U => a) ≤ 𝔠 := calc
  _ ≤ #({a} : Set A) := Cardinal.mk_le_mk_of_subset (by
    rintro _ ⟨x, rfl⟩; exact Set.mem_singleton a)
  _ ≤ 𝔠 := by simpa using (Cardinal.nat_lt_continuum 1).le

/-- The subring of `U → A` of functions having at most continuum many distinct values. -/
def boundedSubring (U A : Type) [CommRing A] : Subring (U → A) where
  carrier := {f | #(Set.range f) ≤ 𝔠}
  zero_mem' := mk_range_const_le 0
  one_mem' := mk_range_const_le 1
  add_mem' hf hg := mk_range_map₂_le (· + ·) hf hg
  mul_mem' hf hg := mk_range_map₂_le (· * ·) hf hg
  neg_mem' {f} hf := by
    have : Set.range (-f) = Neg.neg '' Set.range f := by rw [← Set.range_comp]; rfl
    exact show #(Set.range (-f)) ≤ 𝔠 from (this ▸ Cardinal.mk_image_le).trans hf

/-- Restriction along `g : V → U`, as a ring homomorphism of bounded-range functions. -/
def boundedSubring.comap {U V : Type} (A : Type) [CommRing A] (g : V → U) :
    boundedSubring U A →+* boundedSubring V A where
  toFun f := ⟨f.val ∘ g, show #(Set.range (f.val ∘ g)) ≤ 𝔠 from
    (Cardinal.mk_le_mk_of_subset (Set.range_comp_subset_range g f.val)).trans f.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The presheaf of commutative rings whose sections over `U` are the functions `U → A`
having at most continuum many distinct values, with pointwise operations. -/
def boundedRing (X : TopCat.{0}) (A : Type) [CommRing A] : X.Presheaf CommRingCat.{0} where
  obj U := CommRingCat.of (boundedSubring U.unop A)
  map i := CommRingCat.ofHom (boundedSubring.comap A i.unop)
  map_id _ := rfl
  map_comp _ _ := CommRingCat.hom_ext (RingHom.ext fun _ => rfl)

/-- The underlying function of a section. -/
abbrev fn {X : TopCat.{0}} {A : Type} [CommRing A] {U : Opens X}
    (s : ToType ((boundedRing X A).obj (op U))) : U → A :=
  (s : boundedSubring U A).val

/-- Sections are determined by their underlying functions. -/
lemma fn_injective {X : TopCat.{0}} {A : Type} [CommRing A] {U : Opens X} :
    Function.Injective (fn : ToType ((boundedRing X A).obj (op U)) → U → A) :=
  fun _ _ h => Subtype.ext h

lemma mk_range_fn_le {X : TopCat.{0}} {A : Type} [CommRing A] {U : Opens X}
    (s : ToType ((boundedRing X A).obj (op U))) : #(Set.range (fn s)) ≤ 𝔠 :=
  (s : boundedSubring U A).property

/-- The condition tested by the AFP predicate holds: over any cover with at most continuum
many members, every compatible family of sections of the ring-valued presheaf has a
unique gluing. -/
theorem boundedRing_gluing_of_small_index (X : TopCat.{0}) (A : Type) [CommRing A] {ι : Type}
    (hι : #ι ≤ 𝔠) (U : ι → Opens X)
    (sf : ∀ i, ToType ((boundedRing X A).obj (op (U i))))
    (hc : TopCat.Presheaf.IsCompatible (boundedRing X A) U sf) :
    ∃! s : ToType ((boundedRing X A).obj (op (iSup U))),
      TopCat.Presheaf.IsGluing (boundedRing X A) U sf s := by
  obtain ⟨g, hg, huniq⟩ := (TopCat.Presheaf.toType_isSheaf X A).isSheafUniqueGluing_types
    (fun i => fn (sf i)) (fun i j => congrArg fn (hc i j))
  have range_sub : Set.range g ⊆ ⋃ i, Set.range (fn (sf i)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact Set.mem_iUnion.mpr ⟨i, ⟨⟨x.val, hi⟩, (congr_fun (hg i) ⟨x.val, hi⟩).symm⟩⟩
  have bound : #(Set.range g) ≤ 𝔠 := calc
    _ ≤ #(⋃ i, Set.range (fn (sf i))) := Cardinal.mk_le_mk_of_subset range_sub
    _ ≤ #ι * ⨆ i, #(Set.range (fn (sf i))) := Cardinal.mk_iUnion_le _
    _ ≤ 𝔠 * 𝔠 := mul_le_mul' hι (ciSup_le' fun i => mk_range_fn_le (sf i))
    _ = 𝔠 := Cardinal.continuum_mul_self
  refine ⟨(⟨g, bound⟩ : boundedSubring _ A), fun i => fn_injective (hg i), ?_⟩
  intro t ht
  exact fn_injective (huniq (fn t) fun i => congrArg fn (ht i))

def discreteSpace (A : Type) : TopCat := @TopCat.of A ⊥

def point {A : Type} (a : A) : Opens (discreteSpace A) := ⟨{a}, by trivial⟩

/-- The constant section with value `a` over the open point `{a}`. -/
def pointSection {A : Type} [CommRing A] (a : A) :
    ToType ((boundedRing (discreteSpace A) A).obj (op (point a))) :=
  (⟨fun _ => a, mk_range_const_le a⟩ : boundedSubring (point a) A)

lemma pointSections_compatible (A : Type) [CommRing A] :
    TopCat.Presheaf.IsCompatible (boundedRing (discreteSpace A) A) point pointSection := by
  intro a b
  apply fn_injective
  funext x
  change a = b
  exact (Set.mem_singleton_iff.mp x.property.1).symm.trans
    (Set.mem_singleton_iff.mp x.property.2)

/-- The cover by points is indexed by `A` itself; when `#A > 𝔠` the compatible family
`pointSection` has no gluing, so the presheaf of commutative rings is not a sheaf. -/
theorem boundedRing_not_isSheaf (A : Type) [CommRing A] (hA : 𝔠 < #A) :
    ¬ (boundedRing (discreteSpace A) A).IsSheaf := by
  intro h
  obtain ⟨s, hs, _⟩ := h.isSheafUniqueGluing point pointSection (pointSections_compatible A)
  have surj : Function.Surjective (fn s) := by
    intro a
    let x : ↥(iSup (point : A → Opens (discreteSpace A))) :=
      ⟨a, Opens.mem_iSup.mpr ⟨a, rfl⟩⟩
    exact ⟨x, congr_fun (congrArg fn (hs a)) ⟨a, rfl⟩⟩
  have small : #A ≤ 𝔠 := by
    simpa [Set.range_eq_univ.mpr surj] using mk_range_fn_le s
  exact (not_le_of_gt hA) small

/-- Mathlib's sheaf condition for presheaves of commutative rings rejects the bounded-range
presheaf with coefficients in the commutative ring `ℝ → ℤ`. -/
theorem largeRing_not_isSheaf_commRing :
    ¬ (boundedRing (discreteSpace (ℝ → ℤ)) (ℝ → ℤ)).IsSheaf := by
  apply boundedRing_not_isSheaf
  simpa [Cardinal.mk_real] using Cardinal.cantor' (#ℝ) (by simp : 1 < #ℤ)

/-- The same statement in terms of Mathlib's unique-gluing form of the sheaf condition. -/
theorem largeRing_not_isSheafUniqueGluing_commRing :
    ¬ (boundedRing (discreteSpace (ℝ → ℤ)) (ℝ → ℤ)).IsSheafUniqueGluing :=
  fun h => largeRing_not_isSheaf_commRing
    ((TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr h)

/-- Hartshorne's Proposition II.1.1, as proved in Mathlib: a morphism of sheaves of commutative
rings that induces an isomorphism on every stalk is an isomorphism. -/
theorem isIso_of_stalkwise_iso {X : TopCat.{0}} {F G : TopCat.Sheaf CommRingCat.{0} X}
    (f : F ⟶ G) [∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{0} x).map f.1)] :
    IsIso f :=
  TopCat.Presheaf.isIso_of_stalkFunctor_map_iso f

end SchemesAudit

#print axioms SchemesAudit.boundedRing_gluing_of_small_index
#print axioms SchemesAudit.largeRing_not_isSheaf_commRing
#print axioms SchemesAudit.largeRing_not_isSheafUniqueGluing_commRing
#print axioms SchemesAudit.isIso_of_stalkwise_iso
