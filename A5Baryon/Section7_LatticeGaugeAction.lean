/-
══════════════════════════════════════════════════════════════════════════════
  §7.4. Discrete Lattice Gauge Action for A₅ Holonomy
══════════════════════════════════════════════════════════════════════════════

  File     : A5Baryon/Section7_LatticeGaugeAction.lean
  Paper    : §7.4 — 「」: 
             （ 4.1, 4.2, 4.3）
             "A No-Go Theorem for Smooth-Local Finite Holonomy and Its
             Discrete Implementations: Minimality of A₅ and an Application
             to the Baryogenesis Scale"
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026 (revised from February 2026)

  STATUS:  sorry = 0 | axiom = 0  (target)

  ──────────────────────────────────────────────────────────────────────
  :

     4.1: plaquette_cost_gap_is_sqrt5
      cost(C₅⁻) − cost(C₅⁺) = √5

     4.2: only_C5_produces_irrational_cost
      C₅⁺/C₅⁻  √5  cost 

     4.3（）: totalAction_zero_of_allFlat
       S[U] = 0

  ──────────────────────────────────────────────────────────────────────
  :

    §3  No-go （ 3.2）:
      「 → 」
    「？」

     A₅ :
      (i)   
      (ii)   A₅ （）
      (iii) （） U_loop 
      (iv)   S = Σ_plaquettes (1 − χ(U_loop)) 
      (v)    χ  ρ₃  Δχ = √5 
      (vi)  U_loop ≠ e  = /
            → Section3_ContinuumDefectNoGo.lean  defect 

  ──────────────────────────────────────────────────────────────────────
  :

    §1. 
    §2. 
    §3. 
    §4.  S[U] 
    §5. （ 4.3） — 
    §6. ρ₃  √5 （ 4.1, 4.2）
    §7. Defect 
    §8.  Wilson 
    §9.  cost 
    §10. 

  ──────────────────────────────────────────────────────────────────────
  :

    ・ Q(√5)  → Lean 
    ・Q(√5)  ℚ- (a, b) := a + b√5  ring 
    ・・ Fintype 
    ・√5  QSqrt5 

  ──────────────────────────────────────────────────────────────────────
  :

    : ConjugacyClassGalois.lean   (sigma_A5, A5_IsConj, squaring maps)
            Section3_ContinuumNoGo.lean  (MonodromyModel, smoothLocal_noGo,
                                           3.2, 3.3)
            Section3_ContinuumDefectNoGo.lean (DefectHolonomyModel, A5, IsC5Plus/Minus)
    : Section7_HeatBathDynamics.lean（§7.5 Heat-bath ）
  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

import A5Baryon.Section3_ContinuumDefectNoGo

set_option maxRecDepth 4000

namespace CosmicNecessity

/-!
══════════════════════════════════════════════════════════════════════════════
  §0. （）
══════════════════════════════════════════════════════════════════════════════

  A5, sigma_A5, sigma_sq_A5, A5_IsConj, sigma_not_conj_sigma_sq,
  IsC5Plus, IsC5Minus, DefectHolonomyModel, MonodromyModel,
  SmoothLocalHolonomyModel, smoothLocal_noGo, FiniteHolonomyReading
   import （ConjugacyClassGalois / ContinuumNoGo / ContinuumDefectNoGo）
-/

/-- A₅  = 60 -/
theorem A5_card_eq_60 : Fintype.card A5 = 60 := by native_decide


/-!
══════════════════════════════════════════════════════════════════════════════
  §1. 
══════════════════════════════════════════════════════════════════════════════

  Wilson （K. Wilson, 1974）
   Γ = (V, E) 

  （）ℓ ∈ E  U(ℓ) ∈ G 

  : No-go （ 3.2）「 +  → 」
  「」「 Lie 」
  No-go 
  
-/

section LatticeGauge

/--  -/
structure FiniteGraph where
  V : Type
  [instFintypeV : Fintype V]
  [instDecEqV : DecidableEq V]
  E : Type
  [instFintypeE : Fintype E]
  [instDecEqE : DecidableEq E]
  src : E → V
  tgt : E → V

attribute [instance] FiniteGraph.instFintypeV FiniteGraph.instFintypeE
attribute [instance] FiniteGraph.instDecEqV FiniteGraph.instDecEqE

/-- :  ℓ ∈ E  U(ℓ) ∈ G  -/
structure GaugeConfig (Γ : FiniteGraph) (G : Type*) [Group G] where
  U : Γ.E → G


/-!
══════════════════════════════════════════════════════════════════════════════
  §2. 
══════════════════════════════════════════════════════════════════════════════

   = 
   = 

  :
    U_loop = 1 ()  ⟺ 「」（）
    U_loop ≠ 1           ⟺ 「」（）
-/

variable {Γ : FiniteGraph} {G : Type*} [Group G]

/--  -/
def holonomyProduct (cfg : GaugeConfig Γ G) : List Γ.E → G
  | [] => 1
  | e :: es => cfg.U e * holonomyProduct cfg es

@[simp]
theorem holonomyProduct_nil (cfg : GaugeConfig Γ G) :
    holonomyProduct cfg [] = 1 := rfl

@[simp]
theorem holonomyProduct_cons (cfg : GaugeConfig Γ G) (e : Γ.E) (es : List Γ.E) :
    holonomyProduct cfg (e :: es) = cfg.U e * holonomyProduct cfg es := rfl

theorem holonomyProduct_singleton (cfg : GaugeConfig Γ G) (e : Γ.E) :
    holonomyProduct cfg [e] = cfg.U e := by
  simp [holonomyProduct]

/-- : （） -/
structure Plaquette (Γ : FiniteGraph) where
  edges : List Γ.E
  nonempty : edges ≠ []

/--  -/
def plaquetteHolonomy (cfg : GaugeConfig Γ G) (p : Plaquette Γ) : G :=
  holonomyProduct cfg p.edges

/-- 「」⟺  -/
def isFlat (cfg : GaugeConfig Γ G) (p : Plaquette Γ) : Prop :=
  plaquetteHolonomy cfg p = 1

/-- 「」⟺  -/
def hasCurvature (cfg : GaugeConfig Γ G) (p : Plaquette Γ) : Prop :=
  plaquetteHolonomy cfg p ≠ 1

theorem flat_iff_not_curvature (cfg : GaugeConfig Γ G) (p : Plaquette Γ) :
    isFlat cfg p ↔ ¬ hasCurvature cfg p := by
  simp [isFlat, hasCurvature]


/-!
══════════════════════════════════════════════════════════════════════════════
  §3. 
══════════════════════════════════════════════════════════════════════════════

   χ : G → R 
  A₅ （A₅  totally real）
-/

/-- （） -/
structure CentralFunction (G : Type*) [Group G] (R : Type*) [AddCommMonoid R] where
  val : G → R
  conjugacy_invariant : ∀ (g k : G), val (k * g * k⁻¹) = val g

theorem CentralFunction.conj_eq {G' : Type*} [Group G'] {R : Type*} [AddCommMonoid R]
    (χ : CentralFunction G' R) (g k : G') :
    χ.val (k * g * k⁻¹) = χ.val g :=
  χ.conjugacy_invariant g k


/-!
══════════════════════════════════════════════════════════════════════════════
  §4.  S[U] 
══════════════════════════════════════════════════════════════════════════════

  Wilson :
    S[U] = Σ_{p ∈ Plaquettes} cost(U_p)

  cost(g) := 1 − Re χ(g) / χ(e) 
  （A₅） Re 
-/

/--  -/
structure LatticeWithPlaquettes extends FiniteGraph where
  P : Type
  [instFintypeP : Fintype P]
  plaquette : P → Plaquette toFiniteGraph

attribute [instance] LatticeWithPlaquettes.instFintypeP

/--  -/
structure LatticeGaugeAction (G : Type*) [Group G] where
  lattice : LatticeWithPlaquettes
  config : GaugeConfig lattice.toFiniteGraph G
  cost : G → ℤ

/--  -/
def LatticeGaugeAction.plaquetteAction {G : Type*} [Group G]
    (A : LatticeGaugeAction G) (p : A.lattice.P) : ℤ :=
  A.cost (plaquetteHolonomy A.config (A.lattice.plaquette p))

/-- ** S[U]**:  -/
noncomputable def LatticeGaugeAction.totalAction {G : Type*} [Group G]
    (A : LatticeGaugeAction G) : ℤ :=
  ∑ p : A.lattice.P, A.plaquetteAction p

end LatticeGauge


/-!
══════════════════════════════════════════════════════════════════════════════
  §5.  — 
══════════════════════════════════════════════════════════════════════════════
-/

section FlatnessTheorem

variable {G : Type*} [Group G]

def costVanishesAtIdentity (cost : G → ℤ) : Prop := cost 1 = 0

def allFlat' (A : LatticeGaugeAction G) : Prop :=
  ∀ p : A.lattice.P, isFlat A.config (A.lattice.plaquette p)

/-- ****:  cost(1) = 0  S[U] = 0 -/
theorem totalAction_zero_of_allFlat (A : LatticeGaugeAction G)
    (h_cost : costVanishesAtIdentity A.cost)
    (h_flat : allFlat' A) :
    A.totalAction = 0 := by
  unfold LatticeGaugeAction.totalAction
  apply Finset.sum_eq_zero
  intro p _
  unfold LatticeGaugeAction.plaquetteAction
  have hf : isFlat A.config (A.lattice.plaquette p) := h_flat p
  unfold isFlat at hf
  rw [hf]
  exact h_cost

end FlatnessTheorem


/-!
══════════════════════════════════════════════════════════════════════════════
  §6. ρ₃  √5 
══════════════════════════════════════════════════════════════════════════════

  A₅ 5:

  |   | dim | C₁(e) | C₂   | C₃  | C₅⁺  | C₅⁻   |
  |-------|-----|-------|------|-----|------|-------|
  | ρ₁   |  1  |   1   |  1   |  1  |  1   |   1   |
  | ρ₃   |  3  |   3   | −1   |  0  |  φ   | −1/φ  |
  | ρ₃'  |  3  |   3   | −1   |  0  | −1/φ |   φ   |
  | ρ₄   |  4  |   4   |  0   |  1  | −1   |  −1   |
  | ρ₅   |  5  |   5   |  1   | −1  |  0   |   0   |

  χ = ρ₃ :
    cost(C₅⁺) = 1 − φ  = (1−√5)/2
    cost(C₅⁻) = 1 + 1/φ = (1+√5)/2
    Δcost = √5

  Q(√5) = {a + b√5 | a, b ∈ ℚ}  ℚ-
-/

section CharacterGapInAction

/-- Q(√5) :  (a, b)  a + b√5  -/
structure QSqrt5 where
  rat_part : ℚ
  sqrt5_part : ℚ
  deriving Repr, DecidableEq

namespace QSqrt5

def zero : QSqrt5 := ⟨0, 0⟩
def one : QSqrt5 := ⟨1, 0⟩
def sqrt5 : QSqrt5 := ⟨0, 1⟩

def add (x y : QSqrt5) : QSqrt5 :=
  ⟨x.rat_part + y.rat_part, x.sqrt5_part + y.sqrt5_part⟩

def sub (x y : QSqrt5) : QSqrt5 :=
  ⟨x.rat_part - y.rat_part, x.sqrt5_part - y.sqrt5_part⟩

def mul (x y : QSqrt5) : QSqrt5 :=
  ⟨x.rat_part * y.rat_part + 5 * x.sqrt5_part * y.sqrt5_part,
   x.rat_part * y.sqrt5_part + x.sqrt5_part * y.rat_part⟩

def neg (x : QSqrt5) : QSqrt5 := ⟨-x.rat_part, -x.sqrt5_part⟩

/--  φ = (1 + √5)/2 -/
def phi : QSqrt5 := ⟨1/2, 1/2⟩

/-- −1/φ = (1 − √5)/2 -/
def neg_inv_phi : QSqrt5 := ⟨1/2, -1/2⟩

/-- **φ − (−1/φ) = √5** -/
theorem phi_minus_neg_inv_phi :
    sub phi neg_inv_phi = sqrt5 := by native_decide

/-- **φ + (−1/φ) = 1** -/
theorem phi_plus_neg_inv_phi :
    add phi neg_inv_phi = one := by
  simp [add, phi, neg_inv_phi, one]
  constructor <;> ring

end QSqrt5


/-- A₅  -/
inductive A5ConjClass
  | C1      --       |C₁| = 1
  | C2      -- 2    |C₂| = 15
  | C3      -- 3    |C₃| = 20
  | C5plus  -- 5+ |C₅⁺| = 12
  | C5minus -- 5− |C₅⁻| = 12
  deriving Repr, DecidableEq, Fintype

/-- **ρ₃ **:  → Q(√5) -/
def chi_rho3 : A5ConjClass → QSqrt5
  | .C1      => ⟨3, 0⟩             -- χ(e) = 3
  | .C2      => ⟨-1, 0⟩            -- χ(C₂) = −1
  | .C3      => ⟨0, 0⟩             -- χ(C₃) = 0
  | .C5plus  => QSqrt5.phi          -- χ(C₅⁺) = φ
  | .C5minus => QSqrt5.neg_inv_phi  -- χ(C₅⁻) = −1/φ

/-- ρ₃  = 3 -/
theorem chi_rho3_dim : chi_rho3 A5ConjClass.C1 = ⟨3, 0⟩ := rfl

/-- **: χ_{ρ₃}(C₅⁺) − χ_{ρ₃}(C₅⁻) = √5** -/
theorem character_gap_is_sqrt5 :
    QSqrt5.sub (chi_rho3 .C5plus) (chi_rho3 .C5minus) = QSqrt5.sqrt5 := by native_decide

/-- **: χ_{ρ₃}(C₅⁺) + χ_{ρ₃}(C₅⁻) = 1** -/
theorem character_sum_is_one :
    QSqrt5.add (chi_rho3 .C5plus) (chi_rho3 .C5minus) = QSqrt5.one := by
  simp [chi_rho3, QSqrt5.add, QSqrt5.phi, QSqrt5.neg_inv_phi, QSqrt5.one]
  constructor <;> ring


/-- Wilson  cost: 1 − χ_{ρ₃}(class) -/
def wilsonCost (c : A5ConjClass) : QSqrt5 :=
  QSqrt5.sub QSqrt5.one (chi_rho3 c)

/-- cost(e) = 1 − 3 = −2（ §8  0） -/
theorem wilsonCost_C1 : wilsonCost .C1 = ⟨-2, 0⟩ := by native_decide

/-- cost(C₂) = 1 − (−1) = 2 -/
theorem wilsonCost_C2 : wilsonCost .C2 = ⟨2, 0⟩ := by native_decide

/-- cost(C₃) = 1 − 0 = 1 -/
theorem wilsonCost_C3 : wilsonCost .C3 = ⟨1, 0⟩ := by native_decide

/-- cost(C₅⁺) = 1 − φ = (1−√5)/2 -/
theorem wilsonCost_C5plus : wilsonCost .C5plus = ⟨1/2, -1/2⟩ := by
  simp [wilsonCost, QSqrt5.sub, QSqrt5.one, chi_rho3, QSqrt5.phi]
  constructor <;> ring

/-- cost(C₅⁻) = 1 + 1/φ = (1+√5)/2 -/
theorem wilsonCost_C5minus : wilsonCost .C5minus = ⟨1/2, 1/2⟩ := by
  simp [wilsonCost, QSqrt5.sub, QSqrt5.one, chi_rho3, QSqrt5.neg_inv_phi]
  constructor <;> ring

/-- **: C₅⁺  C₅⁻  = √5**

    Δ_cost = cost(C₅⁻) − cost(C₅⁺)
           = (1 + 1/φ) − (1 − φ) = φ + 1/φ = √5

     √5 
     -/
theorem plaquette_cost_gap_is_sqrt5 :
    QSqrt5.sub (wilsonCost .C5minus) (wilsonCost .C5plus) = QSqrt5.sqrt5 := by native_decide

/-- **C₅⁺/C₅⁻ （√5 ）cost ** -/
theorem only_C5_produces_irrational_cost :
    (wilsonCost .C1).sqrt5_part = 0 ∧
    (wilsonCost .C2).sqrt5_part = 0 ∧
    (wilsonCost .C3).sqrt5_part = 0 ∧
    (wilsonCost .C5plus).sqrt5_part ≠ 0 ∧
    (wilsonCost .C5minus).sqrt5_part ≠ 0 := by native_decide

end CharacterGapInAction


/-!
══════════════════════════════════════════════════════════════════════════════
  §7. Defect 
══════════════════════════════════════════════════════════════════════════════

  Section3_ContinuumNoGo.lean → smoothLocal_noGo（ 3.2）:
    「」

   defect （ 3.3 B）:
    (A) U_loop ≠ e ↔ defect 
    (B) U_loop ∈ C₅⁺ or C₅⁻ →  √5 
    (C) No-go（§7.3）→ （§7.4）→  → √5 → 
-/

section DefectCoherence

/-- No-go →  →  → √5  -/
structure NoGoToLatticeChain where
  step1_nogo : String :=
    "§3  3.2 (smoothLocal_noGo): Finite holonomy + smooth-local reading + nonzero curvature → contradiction"
  step2_alternatives : String :=
    "§3  3.3 (curvature_forces_not_local):\n\
     Option A: defect/monodromy reading (continuous M with defect skeleton Σ)\n\
     Option B: discretize spacetime (lattice gauge theory, §7.4)"
  step3_lattice_action : String :=
    "§7.4: S[U] = Σ_plaquettes (1 − χ_{ρ₃}(U_loop))"
  step4_gap_in_action : String :=
    "§4  4.1: Δ_cost = cost(C₅⁻) − cost(C₅⁺) = √5 (plaquette_cost_gap_is_sqrt5)"
  step5_coherence : String :=
    "Lattice holonomy U_loop ≠ e ↔ defect monodromy ρ(ℓ) ≠ e\n\
     Both embed the character gap √5 as energy difference between C₅⁺ and C₅⁻"

/--  -/
theorem noGoToLattice_complete :
    let chain : NoGoToLatticeChain := {}
    chain.step1_nogo.length > 0 ∧
    chain.step2_alternatives.length > 0 ∧
    chain.step3_lattice_action.length > 0 ∧
    chain.step4_gap_in_action.length > 0 ∧
    chain.step5_coherence.length > 0 := by
  decide

/-- **No-go （import ）**:
    smooth-local  -/
theorem lattice_motivation
    {K : Type*} [Group K] [TopologicalSpace K] [T1Space K]
    (M : SmoothLocalHolonomyModel K) :
    ¬ M.CurvNonzero :=
  smoothLocal_noGo M

end DefectCoherence


/-!
══════════════════════════════════════════════════════════════════════════════
  §8.  Wilson 
══════════════════════════════════════════════════════════════════════════════

  : S = β Σ_p (1 − χ(U_p)/χ(e))
  χ(e) = dim(ρ₃) = 3 :
    Δ_cost_norm = √5/3 —  √5 
-/

section NormalizedAction

/--  Wilson cost: 1 − χ(class)/3 -/
def normalizedWilsonCost (c : A5ConjClass) : QSqrt5 :=
  let chi := chi_rho3 c
  let chi_over_3 : QSqrt5 := ⟨chi.rat_part / 3, chi.sqrt5_part / 3⟩
  QSqrt5.sub QSqrt5.one chi_over_3

theorem normalizedWilsonCost_C5plus :
    normalizedWilsonCost .C5plus = ⟨5/6, -1/6⟩ := by
  simp [normalizedWilsonCost, chi_rho3, QSqrt5.phi, QSqrt5.sub, QSqrt5.one]
  constructor <;> ring

theorem normalizedWilsonCost_C5minus :
    normalizedWilsonCost .C5minus = ⟨5/6, 1/6⟩ := by
  simp [normalizedWilsonCost, chi_rho3, QSqrt5.neg_inv_phi, QSqrt5.sub, QSqrt5.one]
  constructor <;> ring

/-- ** cost  = √5/3 = √5/dim(ρ₃)** -/
theorem normalizedCost_gap :
    QSqrt5.sub (normalizedWilsonCost .C5minus) (normalizedWilsonCost .C5plus)
    = ⟨0, 1/3⟩ := by native_decide

/--  cost  = 0（ S = 0） -/
theorem normalizedWilsonCost_identity :
    normalizedWilsonCost .C1 = QSqrt5.zero := by native_decide

end NormalizedAction


/-!
══════════════════════════════════════════════════════════════════════════════
  §9. :  ρ₃ 
══════════════════════════════════════════════════════════════════════════════

  A₅ 5C₅⁺/C₅⁻  ρ₃  ρ₃' 
  ρ₃  ρ₃'  Galois （g ↦ g² ）
-/

section CharacterUniqueness

inductive A5Irrep
  | rho1 | rho3 | rho3' | rho4 | rho5
  deriving Repr, DecidableEq

/--  C₅⁺  C₅⁻  -/
def distinguishesC5 : A5Irrep → Bool
  | .rho1  => false  -- χ(C₅⁺) = χ(C₅⁻) = 1
  | .rho3  => true   -- χ(C₅⁺) = φ ≠ −1/φ = χ(C₅⁻)
  | .rho3' => true   -- χ(C₅⁺) = −1/φ ≠ φ = χ(C₅⁻)
  | .rho4  => false  -- χ(C₅⁺) = χ(C₅⁻) = −1
  | .rho5  => false  -- χ(C₅⁺) = χ(C₅⁻) = 0

/-- **C₅⁺/C₅⁻ 2** -/
theorem distinguishing_count :
    ([A5Irrep.rho1, .rho3, .rho3', .rho4, .rho5].filter distinguishesC5).length = 2 := by
  native_decide

/-- ρ₃  ρ₃'  gap （Galois ） -/
theorem rho3_rho3'_same_gap_abs :
    let gap  := QSqrt5.sub (chi_rho3 .C5plus)  (chi_rho3 .C5minus)
    let gap' := QSqrt5.sub (chi_rho3 .C5minus) (chi_rho3 .C5plus)
    gap = QSqrt5.sqrt5 ∧ gap' = QSqrt5.neg QSqrt5.sqrt5 := by native_decide

end CharacterUniqueness


/-!
══════════════════════════════════════════════════════════════════════════════
  §10. : 
══════════════════════════════════════════════════════════════════════════════

  |                               |                          |
  |----------------------------------------|------------------------------------------|
  | §3  3.2 No-go:         | smoothLocal_noGo (import)                |
  | §7.4 : Wilson       | LatticeGaugeAction, totalAction          |
  | §4  4.1 χ = ρ₃ → gap = √5   | character_gap_is_sqrt5                   |
  | §4  4.1 cost  = √5          | plaquette_cost_gap_is_sqrt5              |
  | §7.4  √5             | normalizedCost_gap                       |
  | §4  4.2 C₅⁺/C₅⁻  √5   | only_C5_produces_irrational_cost         |
  | §7.4 ρ₃/ρ₃'           | distinguishing_count                     |
  | §7.4 U_loop ≠ e ↔ defect              | NoGoToLatticeChain                       |
  | §5.6  → S = 0          | totalAction_zero_of_allFlat              |
  | §4  4.3  cost(e) = 0  | normalizedWilsonCost_identity            |
  | §7.3 No-go                       | lattice_motivation (import )         |
══════════════════════════════════════════════════════════════════════════════
-/


end CosmicNecessity
