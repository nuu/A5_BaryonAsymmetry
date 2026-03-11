/-
══════════════════════════════════════════════════════════════════════════════
  §3. Continuum No-go: Finite Local Holonomy vs Curvature
══════════════════════════════════════════════════════════════════════════════

  File     : A5Baryon/Section3_ContinuumNoGo.lean
  Paper    : §3 —  No-go （ 3.2, 3.3）
             "A No-Go Theorem for Smooth-Local Finite Holonomy and Its
             Discrete Implementations: Minimality of A₅ and an Application
             to the Baryogenesis Scale"
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026 (revised from February 2026)

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  :

     3.2（No-go）: smoothLocal_noGo
      「smooth-local 」

     3.3（）: curvature_forces_not_local
      「 FiniteHolonomyReading  .local 」
      →  defect/monodromy （）

  ──────────────────────────────────────────────────────────────────────
  :

    No-go :

      (i)    F 
      (ii)   Lie 
      (iii)  ⇒                [TopologyFiniteConnected.lean]
    ★ (iv)   ⇒            [Ambrose–Singer: ]
    ★ (v)    smooth-local  [ Core No-go]

    「」（ 3.3）:
      
      smooth-local  defect/monodromy 

  ──────────────────────────────────────────────────────────────────────
  :

    ・(iii)  TopologyFiniteConnected.lean  Lean 
      →  `[Fintype Hol]` `[ConnectedSpace Hol]` 
    ・(iv) Ambrose–Singer 
      Mathlib  → structure 
      （ mathlib  discharge ）
    ・ CurvNonzero  curv_nonzero_forces_nontrivial 
      2（）

  ──────────────────────────────────────────────────────────────────────
  :

    : TopologyFiniteConnected.lean, Mathlib
    : Section3_ContinuumDefectNoGo.lean（§3.1 Defect/C₅ ）
  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

import A5Baryon.TopologyFiniteConnected

set_option maxRecDepth 4000

namespace CosmicNecessity


/-!
══════════════════════════════════════════════════════════════════════════════
  §1. Defect/Monodromy Model（/）
══════════════════════════════════════════════════════════════════════════════

  No-go  smooth-local 「」
   M° = M \ Σ 
   Σ 
-/

/-- /:
     -/
structure MonodromyModel.{u} (K : Type u) [Group K] where
  Loop : Type u
  [instLoopGroup : Group Loop]
  ρ : Loop →* K

attribute [instance] MonodromyModel.instLoopGroup


/-!
══════════════════════════════════════════════════════════════════════════════
  §2. Smooth-Local Holonomy Model（）
══════════════════════════════════════════════════════════════════════════════

   A1 「
  （）」
-/

structure SmoothLocalHolonomyModel (K : Type*)
    [Group K] [TopologicalSpace K] [T1Space K] where
  /-- （） -/
  Hol : Subgroup K
  /-- A1 「」: Hol  -/
  [instFintypeHol : Fintype Hol]
  /--  (ii):  -/
  [instConnectedHol : ConnectedSpace Hol]
  /-- 「」（） -/
  CurvNonzero : Prop
  /-- Ambrose–Singer  (iv):
       -/
  curv_nonzero_forces_nontrivial : CurvNonzero → Hol ≠ ⊥

attribute [instance] SmoothLocalHolonomyModel.instFintypeHol
attribute [instance] SmoothLocalHolonomyModel.instConnectedHol


/-!
### Core Lemma:  +  ⇒ 
-/

theorem hol_trivial_of_finite_connected
    {K : Type*} [Group K] [TopologicalSpace K] [T1Space K]
    (M : SmoothLocalHolonomyModel K) :
    M.Hol = ⊥ :=
  subgroup_eq_bot_of_fintype_t1_connected (G := K) M.Hol


/-!
### Core No-go (v): 
-/

/-- ** 3.2（No-go）**: smooth-local 
     §3: 「」 -/
theorem smoothLocal_noGo
    {K : Type*} [Group K] [TopologicalSpace K] [T1Space K]
    (M : SmoothLocalHolonomyModel K) :
    ¬ M.CurvNonzero := by
  intro hC
  have hHol : M.Hol = ⊥ := hol_trivial_of_finite_connected M
  exact (M.curv_nonzero_forces_nontrivial hC) hHol


/-- ****: smooth-local  CurvNonzero  -/
theorem localReading_blocks_curvature
    {K : Type*} [Group K] [TopologicalSpace K] [T1Space K]
    (M : SmoothLocalHolonomyModel K)
    (hC : M.CurvNonzero) :
    False :=
  (smoothLocal_noGo M) hC


/-!
══════════════════════════════════════════════════════════════════════════════
  §3. Forced Branching（）
══════════════════════════════════════════════════════════════════════════════

  （A₅）
  smooth-local  defect/monodromy 
-/

/-- 「」 smooth-local  defect  -/
inductive FiniteHolonomyReading (K : Type*) [Group K] [TopologicalSpace K] [T1Space K] where
  | local  : SmoothLocalHolonomyModel K → FiniteHolonomyReading K
  | defect : MonodromyModel K → FiniteHolonomyReading K


/-- ** 3.3（）**:
    FiniteHolonomyReading  `.local` 
     §3.1: 「 defect/monodromy 」 -/
theorem curvature_forces_not_local
    {K : Type*} [Group K] [TopologicalSpace K] [T1Space K]
    (R : FiniteHolonomyReading K)
    (Curv : Prop)
    (hCurv : Curv)
    (Curv_impl :
      ∀ M : SmoothLocalHolonomyModel K,
        R = FiniteHolonomyReading.local M → M.CurvNonzero) :
    (∀ M : SmoothLocalHolonomyModel K, R ≠ FiniteHolonomyReading.local M) := by
  intro M hEq
  exact absurd (Curv_impl M hEq) (smoothLocal_noGo M)


end CosmicNecessity
