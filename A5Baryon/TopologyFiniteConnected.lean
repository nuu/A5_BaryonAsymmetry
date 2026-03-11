/-
══════════════════════════════════════════════════════════════════════════════
  Finite T₁ spaces are discrete; connected + finite ⇒ subsingleton
══════════════════════════════════════════════════════════════════════════════

  File     : A5Baryon/TopologyFiniteConnected.lean
  Paper    : §7.X — Continuum No-go 
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  :

    No-go :
      (i)   
      (ii)   Lie 
    ★ (iii)   ⇒                     ← 
      (iv)  Ambrose–Singer:  ⇒ 
      (v)   「」「」

     (iii) :
      1.  T₁ （）
      2.  T₁  subsingleton
      3. :  T₁  (⊥)

     Lie 
    No-go 「 ×  ⇒ 」 Lean 

  ──────────────────────────────────────────────────────────────────────
  :

    : Mathlib （）
    : Section3_ContinuumNoGo.lean（ No-go）
  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

set_option maxRecDepth 4000

namespace CosmicNecessity

open Set


/-!
## 1. Finite + T₁ ⇒ singletons are open

   T₁ 
  （T₁  →  → ）

  「 T₁ 」
-/

theorem isOpen_singleton_of_fintype_t1
    {α : Type*} [TopologicalSpace α] [T1Space α] [Fintype α]
    (a : α) : IsOpen ({a} : Set α) := by
  classical
  have hfin : (({a} : Set α)ᶜ).Finite :=
    Set.finite_univ.subset (by intro x hx; trivial)
  have hclosed : IsClosed (({a} : Set α)ᶜ) := hfin.isClosed
  exact compl_compl ({a} : Set α) ▸ hclosed.isOpen_compl


/-!
## 2. Connected + finite + T₁ ⇒ subsingleton

   T₁ 々1
  :  → {x}  {x}ᶜ  univ  →
   univ ⊆ {x}  →  x 
-/

/-- :  T₁  `x`  `univ ⊆ {x}`.
     `x`  -/
private theorem eq_of_fintype_t1_connected
    {α : Type*} [TopologicalSpace α] [T1Space α] [Fintype α] [ConnectedSpace α]
    (x a : α) : x = a := by
  by_contra h
  have hUopen : IsOpen ({x} : Set α) := isOpen_singleton_of_fintype_t1 x
  have hVopen : IsOpen ({x}ᶜ : Set α) := (isClosed_singleton (x := x)).isOpen_compl
  have hsub : (Set.univ : Set α) ⊆ {x} ∪ {x}ᶜ := by simp
  have hU_ne : (Set.univ ∩ {x} : Set α).Nonempty := ⟨x, trivial, rfl⟩
  have hV_ne : (Set.univ ∩ {x}ᶜ : Set α).Nonempty := ⟨a, trivial, fun h' => h h'.symm⟩
  have hpre : IsPreconnected (Set.univ : Set α) := isPreconnected_univ
  obtain ⟨z, _, hz1, hz2⟩ := hpre {x} {x}ᶜ hUopen hVopen hsub hU_ne hV_ne
  exact hz2 hz1


theorem subsingleton_of_fintype_t1_connected
    {α : Type*} [TopologicalSpace α] [T1Space α] [Fintype α] [ConnectedSpace α] :
    Subsingleton α := by
  classical
  let a : α := Classical.choice (show Nonempty α from inferInstance)
  exact ⟨fun x y =>
    (eq_of_fintype_t1_connected x a).trans (eq_of_fintype_t1_connected y a).symm⟩


/-!
## 3. Subgroup-level corollary: finite + connected subgroup is ⊥

  :  T₁ 
  Lie  G  H  H = {e}
-/

theorem subgroup_eq_bot_of_subsingleton
    {G : Type*} [Group G] (H : Subgroup G) [Subsingleton H] :
    H = ⊥ := by
  classical
  ext g
  constructor
  · intro hg
    have hEq : (⟨g, hg⟩ : H) = (1 : H) := Subsingleton.elim _ _
    have : (⟨g, hg⟩ : H).1 = (1 : H).1 := congrArg Subtype.val hEq
    simpa using this
  · intro hg
    rw [Subgroup.mem_bot] at hg
    rw [hg]; exact H.one_mem


/-- **No-go (iii) **:  T₁  (⊥)  -/
theorem subgroup_eq_bot_of_fintype_t1_connected
    {G : Type*} [Group G] [TopologicalSpace G] [T1Space G]
    (H : Subgroup G) [Fintype H] [ConnectedSpace H] :
    H = ⊥ := by
  classical
  have : Subsingleton H := subsingleton_of_fintype_t1_connected (α := H)
  exact subgroup_eq_bot_of_subsingleton H


end CosmicNecessity
