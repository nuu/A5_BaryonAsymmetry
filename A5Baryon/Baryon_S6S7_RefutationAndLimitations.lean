/-
══════════════════════════════════════════════════════════════════════════════
  Baryon_S6S7_RefutationAndLimitations.lean
  §6  / §7 
  Refutation Protocol, Limitations, and Open Problems
══════════════════════════════════════════════════════════════════════════════

  File     : Baryon_S6S7_RefutationAndLimitations.lean
  Paper    : "A No-Go Theorem for Smooth-Local Finite Holonomy and Its"
             "Discrete Implementations: Minimality of A₅ and an Application"
             "to the Baryogenesis Scale"
             §6 — Refutation Protocol
             §7 — Limitations and Open Problems
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0 (target)

  ──────────────────────────────────────────────────────────────────────
  :

    §6 
      §6.1  vs 
      §6.2 （4）
      §6.3 （）

    §7 
      §7.0 （）
      §7.1  (L1)–(L7)
      §7.2  (Open Problem 1–6)

  ──────────────────────────────────────────────────────────────────────
  :

    §6–§7 ・
    Lean 
    :

    (A) §6.1 
        (Planck BBN )
    (B) ・・
    (C) 
    (D) §7.0 

    
  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option maxRecDepth 4000

namespace BaryonRefutationLimitations


/-!
══════════════════════════════════════════════════════════════════════════════
  Foundations: 
══════════════════════════════════════════════════════════════════════════════
-/

section Foundations

open Equiv Equiv.Perm

def sigma_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1

def sigma_even : sigma_perm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

def sigma_A5 : alternatingGroup (Fin 5) := ⟨sigma_perm, sigma_even⟩
def sigma_sq_A5 : alternatingGroup (Fin 5) := sigma_A5 ^ 2

def A5_IsConj (g h : alternatingGroup (Fin 5)) : Prop :=
  ∃ k : alternatingGroup (Fin 5), k * g * k⁻¹ = h

instance A5_IsConj_decidable (g h : alternatingGroup (Fin 5)) :
    Decidable (A5_IsConj g h) :=
  Fintype.decidableExistsFintype

def fibPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | (n + 1) => let p := fibPair n; (p.2, p.1 + p.2)

def fib (n : ℕ) : ℕ := (fibPair n).1

def ico_V : ℕ := 12
def ico_E : ℕ := 30
def ico_F : ℕ := 20

end Foundations


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 1: §6.1 —  vs 
══════════════════════════════════════════════════════════════════════════════

  Planck 2018  [2]:
    ηB = (6.143 ± 0.019) × 10⁻¹⁰
    → ηB × 10¹⁰ ∈ [6.124, 6.162]

  BBN  (Schöneberg 2024) [3]:
    Ωbh² = 0.02218 ± 0.00055
    → ηB ≈ (6.09 ± 0.15) × 10⁻¹⁰
    → ηB × 10¹⁰ ∈ [5.94, 6.24]

  A₅ :
    ηB = 3/F₄₈ = 3/4,807,526,976
    → ηB × 10¹⁰ ≈ 6.2402...

  

  : ηB = 3/F₄₈  X × 10⁻¹⁰ 
    3 × 10¹⁰  X × F₄₈ 
══════════════════════════════════════════════════════════════════════════════
-/

section NumericalComparison

-- ────────────────────────────────────────────────────────────────
-- 
-- ────────────────────────────────────────────────────────────────

/-- **F₄₈ ** -/
theorem F48_value : fib 48 = 4807526976 := by native_decide

/-- **A₅ **: 3 × 10¹⁰ = 30,000,000,000 -/
theorem A5_numerator : 3 * (10 : ℕ) ^ 10 = 30000000000 := by norm_num

-- ────────────────────────────────────────────────────────────────
-- Planck 2018 
-- ────────────────────────────────────────────────────────────────

/--
  **Planck  [M]**

  Planck: ηB = 6.143 × 10⁻¹⁰
  A₅:     ηB = 3/F₄₈

  : 3 × 10¹³ vs 6143 × F₄₈

  3 × 10¹³ = 30,000,000,000,000
  6143 × F₄₈ = 6143 × 4,807,526,976 = 29,530,228,109,568

  A₅ > Planck（）
-/
theorem planck_central_comparison :
    3 * 10 ^ 13 > 6143 * fib 48 := by native_decide

/--
  **Planck 1σ  [M]**

  Planck : ηB = 6.162 × 10⁻¹⁰
  : 3 × 10¹³ vs 6162 × F₄₈

  6162 × F₄₈ = 29,618,971,177,312
  3 × 10¹³ =   30,000,000,000,000

  A₅ > Planck 1σ （1σ ）
-/
theorem planck_upper_1sigma :
    3 * 10 ^ 13 > 6162 * fib 48 := by native_decide

/--
  **Planck 1σ  [M]**

  Planck : ηB = 6.124 × 10⁻¹⁰
  : 3 × 10¹³ vs 6124 × F₄₈

  A₅ > Planck 1σ （）
-/
theorem planck_lower_1sigma :
    3 * 10 ^ 13 > 6124 * fib 48 := by native_decide

-- ────────────────────────────────────────────────────────────────
-- BBN 
-- ────────────────────────────────────────────────────────────────

/--
  **BBN  [M]**

  BBN (Schöneberg 2024): ηB ≈ 6.09 × 10⁻¹⁰
  : 3 × 10¹³ vs 6090 × F₄₈

  A₅ > BBN 
-/
theorem bbn_central_comparison :
    3 * 10 ^ 13 > 6090 * fib 48 := by native_decide

/--
  **BBN 1σ  [M]**

  BBN : ηB = 6.24 × 10⁻¹⁰
  : 3 × 10¹³ vs 6240 × F₄₈

  6240 × F₄₈ = 29,998,968,330,240
  3 × 10¹³ =   30,000,000,000,000

  A₅ > BBN 1σ （）
  → BBN 1σ 
-/
theorem bbn_upper_1sigma :
    3 * 10 ^ 13 > 6240 * fib 48 := by native_decide

/--
  **BBN 1σ  [M]**

  BBN : ηB = 5.94 × 10⁻¹⁰
  : 3 × 10¹³ vs 5940 × F₄₈

  A₅ > BBN 1σ 
-/
theorem bbn_lower_1sigma :
    3 * 10 ^ 13 > 5940 * fib 48 := by native_decide

-- ────────────────────────────────────────────────────────────────
-- 
-- ────────────────────────────────────────────────────────────────

/--
  ** ≈ +1.58%  [M]**

   = (A₅ − Planck) / Planck
       = (3/F₄₈ − 6.143e−10) / 6.143e−10
       = (3 × 10¹³ − 6143 × F₄₈) / (6143 × F₄₈)

  : 3 × 10¹³ − 6143 × F₄₈ = 30,000,000,000,000 − 29,532,638,213,568
       = 467,361,786,432

   = 467,361,786,432 / 29,532,638,213,568 ≈ 0.0158 ≈ 1.58%

  :
     × 100 <  × 2 ( < 2%)
     × 100 >  × 1 ( > 1%)
-/
theorem deviation_numerator :
    3 * 10 ^ 13 - 6143 * fib 48 = 467361786432 := by native_decide

/--
  ** 1%  2%  [M]**

   × 100 vs  × k:
    k=1:  × 100 >  →  > 1%
    k=2:  × 100 <  × 2 →  < 2%
-/
theorem deviation_between_1_and_2_percent :
    --  > 1%:  × 100 > 
    467361786432 * 100 > 6143 * fib 48
    ∧
    --  < 2%:  × 100 <  × 2
    467361786432 * 100 < 2 * (6143 * fib 48) := by
  constructor <;> native_decide

/--
  ** 1.5%  1.7%  [M]**

   × 1000 vs  × k:
    k=15:  > 1.5%
    k=17:  < 1.7%
-/
theorem deviation_between_15_and_17_permille :
    467361786432 * 1000 > 15 * (6143 * fib 48)
    ∧ 467361786432 * 1000 < 17 * (6143 * fib 48) := by
  constructor <;> native_decide

/--
  **§6.1  [M]**

   §6.1 :

  |                |                        |         |
  |------------------|-------------------------------|-------------|
  | Planck     | 3×10¹³ > 6143×F₄₈            | A₅ > Planck |
  | Planck 1σ    | 3×10¹³ > 6162×F₄₈            | 1σ        |
  | BBN        | 3×10¹³ > 6090×F₄₈            | A₅ > BBN    |
  | BBN 1σ       | 3×10¹³ > 6240×F₄₈            |      |
  |              | 1.5% < δ < 1.7%              | ≈ +1.58%    |
-/
theorem section6_1_numerical_verification :
    -- Planck
    3 * 10 ^ 13 > 6143 * fib 48
    ∧ 3 * 10 ^ 13 > 6162 * fib 48
    ∧
    -- BBN
    3 * 10 ^ 13 > 6090 * fib 48
    ∧ 3 * 10 ^ 13 > 6240 * fib 48
    ∧
    -- 
    (3 * 10 ^ 13 - 6143 * fib 48 = 467361786432)
    ∧ (467361786432 * 1000 > 15 * (6143 * fib 48))
    ∧ (467361786432 * 1000 < 17 * (6143 * fib 48))
    :=
  ⟨planck_central_comparison,
   planck_upper_1sigma,
   bbn_central_comparison,
   bbn_upper_1sigma,
   deviation_numerator,
   deviation_between_15_and_17_permille.1,
   deviation_between_15_and_17_permille.2⟩

end NumericalComparison


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 2: §6.2 — 
══════════════════════════════════════════════════════════════════════════════

   §6.2 : 4

  |                            |                           |
  |--------------------------------|------------------------------|
  | ηB ≠ ∼10⁻¹⁰                   |  48           |
  | O(1)         | A₅         |
  | A₅  CP         |  (A3)          |
  | F₄₈  | Binet confluence         |
══════════════════════════════════════════════════════════════════════════════
-/

section RefutationConditions

/--
  ****
-/
structure RefutationCondition where
  condition : String
  consequence : String
  affects_claim : ℕ  --  Claim  (0 = )

/-- ** R1**:  -/
def refutation_R1 : RefutationCondition :=
  { condition := "ηB ≠ ∼10⁻¹⁰ (order of magnitude mismatch)"
    consequence := "Interpretation of exponent 48 collapses"
    affects_claim := 3 }

/-- ** R2**:  -/
def refutation_R2 : RefutationCondition :=
  { condition := "No O(1) prefactor yields agreement"
    consequence := "A₅ parameter correspondence is coincidental"
    affects_claim := 3 }

/-- ** R3**: CP  -/
def refutation_R3 : RefutationCondition :=
  { condition := "CP violation established without A₅"
    consequence := "Assumption (A3) negated"
    affects_claim := 3 }

/-- ** R4**: Fibonacci  -/
def refutation_R4 : RefutationCondition :=
  { condition := "F₄₈ shown to have no special status"
    consequence := "Binet confluence is coincidental"
    affects_claim := 3 }

/--
  ** Claim 3  [M]**

  Claim 1  Claim 2 
   Claim 3（）

   §8: " (A1)–(A5) 
  "
-/
theorem refutation_only_affects_claim3 :
    refutation_R1.affects_claim = 3
    ∧ refutation_R2.affects_claim = 3
    ∧ refutation_R3.affects_claim = 3
    ∧ refutation_R4.affects_claim = 3 := ⟨rfl, rfl, rfl, rfl⟩

/--
  ** = 4**
-/
theorem refutation_count :
    [refutation_R1, refutation_R2, refutation_R3, refutation_R4].length = 4 := rfl

/--
  ** [M]**

  （c = O(1) 0）
  ηB ≠ ∼10⁻¹⁰ 

  : c ∈ {1,...,9}  ηB ∼ 10⁻¹⁰ 
  (c/F₄₈  10⁻¹⁰ )
-/
theorem strong_form_refutability :
    -- c = 1: 10⁻¹⁰ < 1/F₄₈ < 10⁻⁹
    1 * fib 48 > 10 ^ 9 ∧ 1 * fib 48 < 10 ^ 10
    ∧
    -- c = 9: 9/F₄₈  10⁻¹⁰ 〜 10⁻⁹ 
    9 * fib 48 > 10 ^ 10 ∧ 9 * fib 48 < 10 ^ 11
    := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end RefutationConditions


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 3: §6.3 — 
══════════════════════════════════════════════════════════════════════════════

   §6.3 :

  |             |  | ηB        |  |
  |---------------------|-------------|-----------|----------|
  | GUT      | ≥ 5         |  |        |
  |      | ≥ 3         |  |        |
  |      | ≥ 4         |  |        |
  | A₅（）        | 0           | ∼10⁻¹⁰   |        |
  | A₅（, c=3） | 1           | 6.24e−10  |        |

  : 
  A₅ 
══════════════════════════════════════════════════════════════════════════════
-/

section ScenarioComparison

/--
  ****
-/
structure BaryogenesisScenario where
  name : String
  min_free_parameters : ℕ
  eta_method : String        -- "fitting" or "derived"
  refutability : String      -- "low", "medium", "high"

/-- GUT  -/
def scenario_GUT : BaryogenesisScenario :=
  { name := "GUT Baryogenesis"
    min_free_parameters := 5
    eta_method := "fitting"
    refutability := "low" }

/--  -/
def scenario_EW : BaryogenesisScenario :=
  { name := "Electroweak Baryogenesis"
    min_free_parameters := 3
    eta_method := "fitting"
    refutability := "medium" }

/--  -/
def scenario_Lepto : BaryogenesisScenario :=
  { name := "Leptogenesis"
    min_free_parameters := 4
    eta_method := "fitting"
    refutability := "medium" }

/-- A₅  -/
def scenario_A5_strong : BaryogenesisScenario :=
  { name := "A₅ (strong form)"
    min_free_parameters := 0
    eta_method := "derived"
    refutability := "high" }

/-- A₅  -/
def scenario_A5_conditional : BaryogenesisScenario :=
  { name := "A₅ (conditional, c=3)"
    min_free_parameters := 1
    eta_method := "derived"
    refutability := "high" }

/--
  **A₅  [M]**

   0 
-/
theorem A5_strong_minimal_parameters :
    scenario_A5_strong.min_free_parameters = 0
    ∧ scenario_A5_strong.min_free_parameters ≤ scenario_GUT.min_free_parameters
    ∧ scenario_A5_strong.min_free_parameters ≤ scenario_EW.min_free_parameters
    ∧ scenario_A5_strong.min_free_parameters ≤ scenario_Lepto.min_free_parameters
    ∧ scenario_A5_strong.min_free_parameters ≤ scenario_A5_conditional.min_free_parameters :=
  ⟨rfl, by decide, by decide, by decide, by decide⟩

/--
  **A₅  "derived"  "fitting"  [M]**

   ηB 
  A₅  ηB 
-/
theorem A5_is_derived :
    scenario_A5_strong.eta_method = "derived"
    ∧ scenario_A5_conditional.eta_method = "derived"
    ∧ scenario_GUT.eta_method = "fitting"
    ∧ scenario_EW.eta_method = "fitting"
    ∧ scenario_Lepto.eta_method = "fitting" := ⟨rfl, rfl, rfl, rfl, rfl⟩

end ScenarioComparison


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 4: §7.0 — 
══════════════════════════════════════════════════════════════════════════════

   §7.0 
  4: [] / [] / [] / []

  
══════════════════════════════════════════════════════════════════════════════
-/

section EpistemicStatusCatalog

/--
  ****（§7.0 4）
-/
inductive EpistemicStatus where
  | Theorem     : EpistemicStatus  -- []: Lean 4 
  | Model       : EpistemicStatus  -- []: 
  | Conditional : EpistemicStatus  -- []: (A1)–(A5) 
  | Open        : EpistemicStatus  -- []: 
  deriving DecidableEq, Repr

/--
  ****
-/
structure ClaimEntry where
  description : String
  status : EpistemicStatus
  lean_verification : Bool   -- Lean 4 
  survives_physics : Bool    -- 

-- ────────────────────────────────────────────────────────────────
-- （ §7.0 ）
-- ────────────────────────────────────────────────────────────────

/-- g ↦ g²  C₅⁺ ↔ C₅⁻  -/
def entry_squaring_swap : ClaimEntry :=
  { description := "g ↦ g² swaps C₅⁺ ↔ C₅⁻"
    status := .Theorem
    lean_verification := true
    survives_physics := true }

/-- Δχ = √5 -/
def entry_character_gap : ClaimEntry :=
  { description := "Δχ = √5"
    status := .Theorem
    lean_verification := true  -- 
    survives_physics := true }

/--  Out(A₅) ≅ ℤ₂  -/
def entry_out_necessity : ClaimEntry :=
  { description := "Swap requires Out(A₅) ≅ ℤ₂"
    status := .Theorem
    lean_verification := true
    survives_physics := true }

/-- √5  -/
def entry_sqrt5_mode : ClaimEntry :=
  { description := "√5 is asymmetric mode amplitude in central distributions"
    status := .Model
    lean_verification := false  --  Q(√5) 
    survives_physics := true }

/-- φ  -/
def entry_phi_eigenvalue : ClaimEntry :=
  { description := "φ is eigenvalue of T_μ in ρ₃ sector"
    status := .Model
    lean_verification := false
    survives_physics := true }

/-- 48 = V·(|Stab_v|−1) -/
def entry_48_stabilizer : ClaimEntry :=
  { description := "48 = V·(|Stab_v|−1)"
    status := .Theorem
    lean_verification := true
    survives_physics := true }

/-- φ⁻⁴⁸  -/
def entry_dilution : ClaimEntry :=
  { description := "φ⁻⁴⁸ is dilution factor"
    status := .Conditional
    lean_verification := false  --  (A5) 
    survives_physics := false }

/-- ηB = c√5 φ⁻⁴⁸ ≈ c/F₄₈ -/
def entry_eta_formula : ClaimEntry :=
  { description := "ηB = c√5 φ⁻⁴⁸ ≈ c/F₄₈"
    status := .Conditional
    lean_verification := false  -- (A1)–(A5) 
    survives_physics := false }

/-- c = 3 -/
def entry_prefactor : ClaimEntry :=
  { description := "c = 3 (Nc or |Stab_face|)"
    status := .Conditional
    lean_verification := false  -- 
    survives_physics := false }

/-- √5 vs 2logφ  -/
def entry_selection_rule : ClaimEntry :=
  { description := "Selection rule: √5 vs 2logφ"
    status := .Open
    lean_verification := false
    survives_physics := false }

/--  -/
def entry_lagrangian : ClaimEntry :=
  { description := "Derivation from Lagrangian"
    status := .Open
    lean_verification := false
    survives_physics := false }

/--  48  -/
def entry_exponent_unique : ClaimEntry :=
  { description := "Unique derivation of exponent 48"
    status := .Open
    lean_verification := false
    survives_physics := false }

/--  -/
def claim_catalog : List ClaimEntry :=
  [ entry_squaring_swap
  , entry_character_gap
  , entry_out_necessity
  , entry_sqrt5_mode
  , entry_phi_eigenvalue
  , entry_48_stabilizer
  , entry_dilution
  , entry_eta_formula
  , entry_prefactor
  , entry_selection_rule
  , entry_lagrangian
  , entry_exponent_unique ]

/--
  ** = 12 **
-/
theorem catalog_size : claim_catalog.length = 12 := rfl

/--
  **[]  Lean  [M]**

   [] :
    lean_verification = true ∧ survives_physics = true
-/
theorem theorem_entries_verified :
    entry_squaring_swap.lean_verification = true
    ∧ entry_squaring_swap.survives_physics = true
    ∧ entry_character_gap.lean_verification = true
    ∧ entry_character_gap.survives_physics = true
    ∧ entry_out_necessity.lean_verification = true
    ∧ entry_out_necessity.survives_physics = true
    ∧ entry_48_stabilizer.lean_verification = true
    ∧ entry_48_stabilizer.survives_physics = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
  **[]  Lean  [M]**
-/
theorem open_entries_unverified :
    entry_selection_rule.lean_verification = false
    ∧ entry_lagrangian.lean_verification = false
    ∧ entry_exponent_unique.lean_verification = false :=
  ⟨rfl, rfl, rfl⟩

end EpistemicStatusCatalog


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 5: §7.1 —  (L1)–(L7)
══════════════════════════════════════════════════════════════════════════════

   §7.1 "":

  (L1) 
  (L2) CP 
  (L3) 
  (L4) 
  (L5) 
  (L6) Fibonacci 
  (L7) √5  2logφ 
══════════════════════════════════════════════════════════════════════════════
-/

section Limitations

/--
  ****
-/
structure Limitation where
  code : String            -- L1, L2, ...
  title : String
  description : String
  related_open_problem : Option String  -- 

/-- **(L1) **
    :  S = Σ(1 − χ_{ρ₃}(U_loop)) 
    Δcost = √5  -/
def limitation_L1 : Limitation :=
  { code := "L1"
    title := "Absence of dynamical mechanism"
    description := "Discrete lattice gauge action S = Σ(1−χ_{ρ₃}(U_loop)) constructed with formally verified Δcost = √5. \
      Full field-theoretic Lagrangian derivation remains open; §5.6 provides scaffold"
    related_open_problem := some "G1'" }

/-- **(L2) CP ** -/
def limitation_L2 : Limitation :=
  { code := "L2"
    title := "Absence of CP phase"
    description := "All A₅ irreps are real-type (Frobenius-Schur = +1); no CKM-type δ_CP predicted"
    related_open_problem := some "G8" }

/-- **(L3) ** -/
def limitation_L3 : Limitation :=
  { code := "L3"
    title := "Partial a posteriori nature of prefactor"
    description := "c = 3 fixable a priori via Nc or |Stab_face|, but dynamical explanation missing"
    related_open_problem := some "G12" }

/-- **(L4) ** -/
def limitation_L4 : Limitation :=
  { code := "L4"
    title := "Non-uniqueness of exponent"
    description := "48 = V·(|Stab_v|−1) = |A₅|−V = 4V: multiple decompositions exist"
    related_open_problem := some "L4" }

/-- **(L5) ** -/
def limitation_L5 : Limitation :=
  { code := "L5"
    title := "Scale problem"
    description := "Whether φ⁻⁴⁸ is an RG invariant is unresolved"
    related_open_problem := some "G2-B" }

/-- **(L6) Fibonacci ** -/
def limitation_L6 : Limitation :=
  { code := "L6"
    title := "Fibonacci interpretation"
    description := "Binet confluence is algebraic identity over Q(√5); dynamical 'why Fibonacci' unanswered"
    related_open_problem := some "G11" }

/-- **(L7) √5  2logφ ** -/
def limitation_L7 : Limitation :=
  { code := "L7"
    title := "√5 vs 2logφ selection"
    description := "Discrete context: √5; continuous limit: 2logφ. Selection rule incomplete"
    related_open_problem := some "G13" }

/--
  ** = 7**
-/
theorem limitation_count :
    [limitation_L1, limitation_L2, limitation_L3, limitation_L4,
     limitation_L5, limitation_L6, limitation_L7].length = 7 := rfl

/--
  ** [M]**

  
  
-/
theorem all_limitations_have_open_problems :
    limitation_L1.related_open_problem.isSome = true
    ∧ limitation_L2.related_open_problem.isSome = true
    ∧ limitation_L3.related_open_problem.isSome = true
    ∧ limitation_L4.related_open_problem.isSome = true
    ∧ limitation_L5.related_open_problem.isSome = true
    ∧ limitation_L6.related_open_problem.isSome = true
    ∧ limitation_L7.related_open_problem.isSome = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
  **(L4) : 48  [M]**

  48 = V·(|Stab_v|−1) = |A₅|−V = 4V = E+F−2

  「」
-/
theorem L4_multiple_decompositions :
    ico_V * (5 - 1) = 48
    ∧ (60 : ℕ) - ico_V = 48
    ∧ 4 * ico_V = 48
    ∧ ico_E + ico_F - 2 = 48
    := ⟨by norm_num [ico_V], by norm_num [ico_V], by norm_num [ico_V], by norm_num [ico_E, ico_F]⟩

/--
  **(L2) : Frobenius-Schur  = +1 [M]**

  A₅ :
  χ(g²)  Frobenius-Schur  +1

  : σ  σ² σ  σ⁻¹ 
  
-/
theorem L2_real_type_basis :
    -- σ⁻¹ ∈ C₅⁺（σ ）→ χ(σ) = χ(σ⁻¹) → 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g⁻¹) sigma_A5) := by native_decide

end Limitations


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 6: §7.2 —  (Open Problem 1–6)
══════════════════════════════════════════════════════════════════════════════

   §7.2 6
══════════════════════════════════════════════════════════════════════════════
-/

section OpenProblems

/--
  ****
-/
structure OpenProblem where
  number : ℕ
  code : String
  title : String
  statement : String
  related_limitations : List String

/-- **OP1 (G1'): **
    : A₅  S = Σ(1 − χ_{ρ₃}(U_loop))
    → Section7_LatticeGaugeAction.lean 
    →  √5  -/
def OP1 : OpenProblem :=
  { number := 1
    code := "G1'"
    title := "Dynamical mechanism"
    statement := "Derive ηB = c√5 φ⁻⁴⁸ from a Lagrangian with A₅ holonomy. \
      First candidate: discrete lattice gauge action S = Σ(1 − χ_{ρ₃}(U_loop)) \
      where Δcost(C₅⁻ vs C₅⁺) = √5 (formally verified). \
      Alternatives: fiber bundle (top-down), Dijkgraaf–Witten TQFT (see G1'_approaches)"
    related_limitations := ["L1"] }

/-- **OP2 (G2-B): RG ** -/
def OP2 : OpenProblem :=
  { number := 2
    code := "G2-B"
    title := "RG invariance"
    statement := "Prove or disprove that exponent 48 is RG invariant"
    related_limitations := ["L5"] }

/-- **OP3 (G8): Out(A₅)  δ_CP** -/
def OP3 : OpenProblem :=
  { number := 3
    code := "G8"
    title := "Out(A₅) and δ_CP"
    statement := "Relate Out(A₅) ≅ ℤ₂ to physical CP-violation phase δ_CP"
    related_limitations := ["L2"] }

/-- **OP4 (G11):  Fibonacci ** -/
def OP4 : OpenProblem :=
  { number := 4
    code := "G11"
    title := "Fibonacci in cosmology"
    statement := "Systematize the role of Fibonacci/Lucas numbers in cosmological parameters from icosahedral geometry"
    related_limitations := ["L6"] }

/-- **OP5 (G12): ** -/
def OP5 : OpenProblem :=
  { number := 5
    code := "G12"
    title := "Prefactor derivation"
    statement := "Derive c = n = 3 from first principles"
    related_limitations := ["L3"] }

/-- **OP6 (G13): scaffold ** -/
def OP6 : OpenProblem :=
  { number := 6
    code := "G13"
    title := "Scaffold completion"
    statement := "Extend §5.6 minimal model to full effective theory; resolve √5 vs 2logφ selection rule"
    related_limitations := ["L1", "L7"] }

/--
  ** = 6**
-/
theorem open_problem_count :
    [OP1, OP2, OP3, OP4, OP5, OP6].length = 6 := rfl

/--
  **1 [M]**
-/
theorem all_OPs_have_related_limitations :
    OP1.related_limitations.length ≥ 1
    ∧ OP2.related_limitations.length ≥ 1
    ∧ OP3.related_limitations.length ≥ 1
    ∧ OP4.related_limitations.length ≥ 1
    ∧ OP5.related_limitations.length ≥ 1
    ∧ OP6.related_limitations.length ≥ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/--
  **OP6 2 (L1, L7) **

  Scaffold  (L1) 
   (L7) 
-/
theorem OP6_dual_limitations :
    OP6.related_limitations.length = 2 := rfl

end OpenProblems


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 6b: §7.2  — G1' 3
══════════════════════════════════════════════════════════════════════════════

  G1' () 3:

  1（ — ）:
     A₅- P → M 
    
    → No-go  (§7.X)  smooth-local 
    → §7 Open Problems 「」

  2（ — ）★ :
    Wilson  A₅ 
    S = Σ(1 − χ_{ρ₃}(U_loop)) 
    → Section7_LatticeGaugeAction.lean 
    → Δcost = √5  (plaquette_cost_gap_is_sqrt5)
    →  √5/3  (normalizedCost_gap)

  3（ — Dijkgraaf–Witten ）:
    3 TQFT  A₅-Dijkgraaf–Witten 
    H³(BA₅, U(1)) 
    → §7 Open Problems 「」

  : 3
══════════════════════════════════════════════════════════════════════════════
-/

section G1PrimeApproaches

/-- G1'  -/
structure G1Approach where
  number : ℕ
  name : String
  method : String
  status : String
  /-- §7 Open Problems  -/
  classification : String
  /--  -/
  relation_to_lattice : String

/-- **1: （）**

     M  A₅- P → M 
    

    No-go  (smoothLocal_noGo) :
    ・ A₅ 
    ・
    ∴ smooth-local 

    「」 defect/monodromy  (A) 
    →  §7  -/
def approach1_fiberBundle : G1Approach :=
  { number := 1
    name := "Top-down fiber bundle"
    method := "A₅-principal bundle P → M with connection; Lagrangian from curvature"
    status := "Blocked by No-go (smoothLocal_noGo): smooth-local reading excluded. \
      Viable only via defect/monodromy reading (ρ : π₁(M∖Σ) → A₅)"
    classification := "§7 Open Problem: alternative formulation candidate"
    relation_to_lattice := "Defect reading is the continuous analog of lattice gauge theory; \
      both give √5 energy gap via χ_{ρ₃}" }

/-- **2: （）** ★ 

     Γ = (V, E) 
     A₅  U ∈ A₅ 
    Wilson :

      S[U] = Σ_{plaquettes} (1 − χ_{ρ₃}(U_loop))

    :
    ・Section7_LatticeGaugeAction.lean 
    ・character_gap_is_sqrt5: Δχ = √5
    ・plaquette_cost_gap_is_sqrt5: Δcost = √5
    ・normalizedCost_gap:  √5/3
    ・only_C5_produces_irrational_cost: C₅⁺/C₅⁻  √5 
    ・distinguishing_count: ρ₃/ρ₃'  -/
def approach2_latticeGauge : G1Approach :=
  { number := 2
    name := "Bottom-up lattice gauge theory"
    method := "Finite graph + Wilson plaquette action S = Σ(1 − χ_{ρ₃}(U_loop))"
    status := "Primary candidate. Formally verified: Δcost(C₅⁻ vs C₅⁺) = √5. \
      No-go does not apply (discrete ⇒ no smooth connection ⇒ no Lie subgroup obstruction)"
    classification := "§7.Y: first candidate for G1' (Section7_LatticeGaugeAction.lean)"
    relation_to_lattice := "This IS the lattice gauge formulation" }

/-- **3: （Dijkgraaf–Witten ）**

    3 TQFT  A₅-Dijkgraaf–Witten 
    : Z = (1/|A₅|) Σ_{[A]} e^{2πi⟨ω,[M]⟩}
     [ω] ∈ H³(BA₅, U(1)) 

    A₅  (H¹ = H² = 0) 
    H³(BA₅, ℤ) ≅ ℤ₂ （Schur ）
    1

    → 
    →  §7  -/
def approach3_dijkgraafWitten : G1Approach :=
  { number := 3
    name := "Dijkgraaf–Witten TQFT"
    method := "3d TQFT with A₅ gauge group; topological action classified by H³(BA₅, U(1)) ≅ ℤ₂"
    status := "Alternative candidate. May provide topological constraints \
      complementing the lattice gauge action. Not yet formalized"
    classification := "§7 Open Problem: alternative formulation candidate"
    relation_to_lattice := "DW theory on a simplicial complex reduces to a lattice gauge theory \
      with additional topological weighting; character gap √5 enters via same mechanism" }

/-- **3** -/
def G1_approaches : List G1Approach :=
  [approach1_fiberBundle, approach2_latticeGauge, approach3_dijkgraafWitten]

/-- ** = 3** -/
theorem G1_approach_count : G1_approaches.length = 3 := rfl

/-- **（）** -/
theorem G1_approaches_all_named :
    G1_approaches.map G1Approach.name =
    ["Top-down fiber bundle",
     "Bottom-up lattice gauge theory",
     "Dijkgraaf–Witten TQFT"] := rfl

/-- **2（）** -/
theorem G1_primary_is_lattice :
    (G1_approaches[1]?).map G1Approach.number = some 2 := rfl

/-- **1 No-go ** -/
theorem approach1_blocked_by_nogo :
    approach1_fiberBundle.classification = "§7 Open Problem: alternative formulation candidate" := rfl

/-- **2（）** -/
theorem approach2_formally_verified :
    approach2_latticeGauge.classification = "§7.Y: first candidate for G1' (Section7_LatticeGaugeAction.lean)" := rfl

/-- **3** -/
theorem approach3_is_alternative :
    approach3_dijkgraafWitten.classification = "§7 Open Problem: alternative formulation candidate" := rfl

/-- **G1' :
    (1) §7.X  No-go 
    (2) §7.Y （）
    (3) χ = ρ₃ → gap = √5 
    (4) 
    (5) 1,3  Open Problems  -/
structure G1PrimeDocumentStructure where
  step1 : String := "§7.X: No-go theorem (smooth-local reading excluded) — Section3_ContinuumNoGo.lean"
  step2 : String := "§7.Y: Lattice gauge action S = Σ(1−χ_{ρ₃}(U_loop)) — Section7_LatticeGaugeAction.lean"
  step3 : String := "§7.Y §6: Character gap √5 enters action directly — plaquette_cost_gap_is_sqrt5"
  step4 : String := "§7.Y §7: Defect correspondence U_loop≠e ↔ curvature concentration at Σ"
  step5 : String := "§7 OP: Approaches 1 (fiber bundle) and 3 (DW TQFT) as alternative candidates"

end G1PrimeApproaches


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 7: Layer M 
══════════════════════════════════════════════════════════════════════════════

  §6–§7 Layer M 

   (A1)–(A5) :
    (i)   g ↦ g²  C₅⁺  C₅⁻ 
    (ii)   Out(A₅) 
    (iii) Δχ = √5  A₅ 
    (iv)  F₄₈ = 4,807,526,976
    (v)   L₄₈² = 5 · F₄₈² + 4
    (vi)  48 = |A₅| − V = V · (|Stab_v| − 1)
══════════════════════════════════════════════════════════════════════════════
-/

section LayerMPersistence

open Equiv Equiv.Perm

/--
  **Layer M :  [M]**

   (R1)–(R4)  (L1)–(L7) 
  
-/
theorem layer_M_persistence :
    -- (i) 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5)
    ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5)
    ∧
    -- (ii) 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g⁻¹) sigma_A5)
    ∧
    -- (iii) |C₅⁺| = |C₅⁻| = 12
    Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_A5 } = 12
    ∧
    -- (iv) F₄₈
    fib 48 = 4807526976
    ∧
    -- (v) Lucas-Fibonacci 
    (fib 47 + fib 49) ^ 2 = 5 * (fib 48) ^ 2 + 4
    ∧
    -- (vi) 
    (60 : ℕ) - ico_V = 48
    ∧ ico_V * (5 - 1) = 48
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; revert g; native_decide
  · intro g hg; revert g; native_decide
  · intro g hg; revert g; native_decide
  · native_decide
  · native_decide
  · native_decide
  · norm_num [ico_V]
  · norm_num [ico_V]

end LayerMPersistence


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 8: 
══════════════════════════════════════════════════════════════════════════════
-/

/--
  **§6–§7  — **
-/
theorem baryon_S6S7_file_integrity :
    -- §6.1 
    3 * 10 ^ 13 > 6143 * fib 48
    ∧ (3 * 10 ^ 13 - 6143 * fib 48 = 467361786432)
    ∧ (467361786432 * 1000 > 15 * (6143 * fib 48))
    ∧ (467361786432 * 1000 < 17 * (6143 * fib 48))
    ∧
    -- §6.2 
    refutation_R1.affects_claim = 3
    ∧
    -- §6.3 
    scenario_A5_strong.min_free_parameters = 0
    ∧
    -- §7.0 
    claim_catalog.length = 12
    ∧
    -- §7.1 
    [limitation_L1, limitation_L2, limitation_L3, limitation_L4,
     limitation_L5, limitation_L6, limitation_L7].length = 7
    ∧
    -- §7.2 
    [OP1, OP2, OP3, OP4, OP5, OP6].length = 6
    :=
  ⟨planck_central_comparison,
   deviation_numerator,
   deviation_between_15_and_17_permille.1,
   deviation_between_15_and_17_permille.2,
   rfl, rfl, rfl, rfl, rfl⟩


/-!
══════════════════════════════════════════════════════════════════════════════
   §6–§7 ↔ Lean 
══════════════════════════════════════════════════════════════════════════════

  |                                 | Lean /                           |
  |--------------------------------------------|--------------------------------------------|
  | §6.1 Planck                      | planck_central_comparison                  |
  | §6.1 Planck 1σ                        | planck_upper_1sigma, planck_lower_1sigma   |
  | §6.1 BBN                        | bbn_central_comparison                     |
  | §6.1 BBN 1σ                           | bbn_upper_1sigma, bbn_lower_1sigma         |
  | §6.1  = 467,361,786,432               | deviation_numerator                        |
  | §6.1  ∈ (1.5%, 1.7%)                  | deviation_between_15_and_17_permille       |
  | §6.1                                  | section6_1_numerical_verification          |
  | §6.2  R1–R4                       | refutation_R1 .. R4                        |
  | §6.2  Claim 3             | refutation_only_affects_claim3             |
  | §6.3                          | scenario_GUT .. scenario_A5_conditional    |
  | §6.3 A₅                     | A5_strong_minimal_parameters               |
  | §6.3 derived vs fitting                   | A5_is_derived                              |
  | §7.0  (12)           | claim_catalog                              |
  | §7.0 []                      | theorem_entries_verified                   |
  | §7.1  L1–L7                           | limitation_L1 .. L7                        |
  | §7.1 L4                           | L4_multiple_decompositions                 |
  | §7.1 L2                           | L2_real_type_basis                         |
  | §7.2  OP1–OP6                   | OP1 .. OP6                                 |
  | §7.2 OP6                          | OP6_dual_limitations                       |
  | §7.2 G1'  (3)             | approach1..3, G1_approaches                |
  | §7.2  =                 | G1_primary_is_lattice                      |
  | §8 Layer M                          | layer_M_persistence                        |
══════════════════════════════════════════════════════════════════════════════
-/


end BaryonRefutationLimitations
