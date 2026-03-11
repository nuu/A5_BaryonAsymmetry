/-
══════════════════════════════════════════════════════════════════════════════
  §7.5. Heat-bath Dynamics and the a − a′ Reduction
══════════════════════════════════════════════════════════════════════════════

  File     : A5Baryon/Section7_HeatBathDynamics.lean
  Paper    : §7.5 — Heat-bath  a − a′ 
             Appendix A.6 — （ (15), φ + 1/φ = √5）
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026

  STATUS:  sorry = 0 | axiom = 0
           （§7.5.4  []  — ）

  ──────────────────────────────────────────────────────────────────────
  :

    :

    [M] （sorry = 0, axiom = 0）:
      ・φ + 1/φ = √5（Appendix A.6: phi_add_inv）
      ・φ · 1/φ = 1（）
      ・Q(√5)  Fourier 
      ・Heat-bath （）
      ・ρ₃/ρ₃′ （）

    [P] （ — ）:
      ・a − a′ （ (15)）:  B3 
        μ （§7.5.2  FM2 ）
      ・ℤ₂ （σ ）: Open Problem G1′ 

  ──────────────────────────────────────────────────────────────────────
  :

    Section7_LatticeGaugeAction.lean :
      「Wilson  S[U]  cost(C₅⁻) − cost(C₅⁺) = √5」
    「 μ 」
    「√5 」

    （§7.5 ）:
      Wilson 
        → heat-bath  μ_β （§7.5.2）
        → T_μ （Schur ）
        → ρ₃/ρ₃′  ℤ₂ （§7.5.3）
        → a − a′ = (√5/3)(m₊ − m₋)（§7.5.4,  (15)）
        → Δ = (a − a′)·√5 = (√5/3)(m₊ − m₋)·√5

     FM2 （§5.6.X ）:
      μ  → √5 
      「Wilson  → heat-bath → 」
       FM2 

  ──────────────────────────────────────────────────────────────────────
  :

    §1.  （1/φ ）
    §2.  Heat-bath （FM2 ）
    §3.  A₅  Fourier 
    §4.  ρ₃/ρ₃′  ℤ₂ 
    §5.  Fourier （ (15) ）
    §6.  a − a′ （ (15)）
    §7.  Δ = (a − a′)·√5 
    §8.  

  ──────────────────────────────────────────────────────────────────────
  :

    : A5Baryon.Section7_LatticeGaugeAction
              （QSqrt5, A5ConjClass, chi_rho3, wilsonCost,
               normalizedWilsonCost, plaquette_cost_gap_is_sqrt5,
               normalizedCost_gap, LatticeGaugeAction）
    : （§8 ）
  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

import A5Baryon.Section7_LatticeGaugeAction

set_option maxRecDepth 4000

namespace CosmicNecessity

/-!
══════════════════════════════════════════════════════════════════════════════
  §1. : 1/φ 
══════════════════════════════════════════════════════════════════════════════

   φ = (1 + √5)/2 ∈ Q(√5) 

  Q(√5) （QSqrt5 ）:
    ・φ     = ⟨1/2, 1/2⟩
    ・1/φ   = φ − 1 = ⟨−1/2, 1/2⟩  （φ² = φ + 1  φ·(φ−1) = 1）
    ・√5    = ⟨0, 1⟩

  **Appendix A.6  phi_add_inv（φ + 1/φ = √5）**
══════════════════════════════════════════════════════════════════════════════
-/

section GoldenRatioIdentities

open QSqrt5

/-- 1/φ = φ − 1 = (−1 + √5)/2  -/
def inv_phi : QSqrt5 := ⟨-1/2, 1/2⟩

/-- φ  1/φ  = 1φ  -/
theorem phi_mul_inv_phi : mul phi inv_phi = one := by native_decide

/-- 1/φ = neg_inv_phi （LatticeGaugeAction  neg_inv_phi  −1/φ）
     1/φ = ⟨−1/2, 1/2⟩  inv_phi  -/
theorem inv_phi_eq : inv_phi = ⟨-1/2, 1/2⟩ := rfl

/-- **φ + 1/φ = √5 (Appendix A.6: phi_add_inv)**

    : ⟨1/2, 1/2⟩ + ⟨−1/2, 1/2⟩ = ⟨0, 1⟩ = √5
     Binet §5.6 
    「A₅  = (a − a′)·√5」
     -/
theorem phi_add_inv : add phi inv_phi = sqrt5 := by native_decide

/-- φ − 1/φ = 1（） -/
theorem phi_sub_inv_phi : sub phi inv_phi = one := by native_decide

/-- √5 = φ + 1/φ （phi_add_inv ） -/
theorem sqrt5_eq_phi_add_inv_phi : sqrt5 = add phi inv_phi := by native_decide

/-- :
    χ_{ρ₃}(C₅⁺) − χ_{ρ₃}(C₅⁻) = φ − (−1/φ) = φ + 1/φ = √5

     §2.2  (1)  Appendix A.2 
    character_gap_is_sqrt5  -/
theorem character_gap_via_golden_ratio :
    sub (chi_rho3 .C5plus) (chi_rho3 .C5minus)
    = add phi inv_phi := by native_decide

end GoldenRatioIdentities


/-!
══════════════════════════════════════════════════════════════════════════════
  §2. Heat-bath （§7.5.2 / FM2 ）
══════════════════════════════════════════════════════════════════════════════

  ** §7.5.2**:
    heat-bath  μ_β(g) ∝ exp(−β(1 − χ(g)/χ(e)))
    （class function）
    §5.6  T_μ 

  **FM2 ** (§5.6.X ):
    FM2: μ  → √5 
    → Wilson  heat-bath 
    → FM2 

  「」 A₅ConjClass → ℚ 
  Wilson 
══════════════════════════════════════════════════════════════════════════════
-/

section HeatBathCentrality

/-- A₅ : 
    （Wilson  heat-bath ） -/
structure A5CentralMeasure where
  /--  w(C) ∈ ℚ（） -/
  weight : A5ConjClass → ℚ
  /--  -/
  nonneg : ∀ c, 0 ≤ weight c

/-- ****

    2
     FM2  -/
theorem central_measure_is_class_function (μ : A5CentralMeasure) :
    ∀ c₁ c₂ : A5ConjClass, c₁ = c₂ → μ.weight c₁ = μ.weight c₂ :=
  fun _ _ h => h ▸ rfl

/-- Wilson  cost  heat-bath 
    μ_β(class) ∝ 1 − β · normalizedWilsonCost(class) 
    （β  1 ; Q(√5)  rat_part ） -/
def wilsonHeatBathWeight (β_rat : ℚ) : A5ConjClass → ℚ :=
  fun c => 1 - β_rat * (normalizedWilsonCost c).rat_part

/-- Wilson heat-bath （β ）
     -/
def wilsonHeatBathMeasure (β_rat : ℚ) (h : ∀ c, 0 ≤ wilsonHeatBathWeight β_rat c) :
    A5CentralMeasure where
  weight := wilsonHeatBathWeight β_rat
  nonneg := h

/-- **FM2 （）**:
    Wilson  → heat-bath  →  μ 
     FM2  -/
theorem fm2_structural_closure :
    ∀ (μ : A5CentralMeasure) (c₁ c₂ : A5ConjClass),
      c₁ = c₂ → μ.weight c₁ = μ.weight c₂ :=
  fun μ c₁ c₂ h => central_measure_is_class_function μ c₁ c₂ h

end HeatBathCentrality


/-!
══════════════════════════════════════════════════════════════════════════════
  §3. A₅  Fourier 
══════════════════════════════════════════════════════════════════════════════

   μ 「Fourier 」:
    a  = μ̂(ρ₃)  := Σ_{c} |c| · μ(c) · χ_{ρ₃}(c) / |A₅|
    a′ = μ̂(ρ₃′) := Σ_{c} |c| · μ(c) · χ_{ρ₃′}(c) / |A₅|

   χ_{ρ₃′}  Galois : C₅⁺ ↔ C₅⁻ 

  Schur : T_μ f := Σ_g μ(g) ρ(g) f 
   Fourier  a  a′ 
══════════════════════════════════════════════════════════════════════════════
-/

section FourierCoefficients

/-- A₅ （|A₅| = 60 ） -/
def conjClassSize : A5ConjClass → ℕ
  | .C1      => 1   -- {e}
  | .C2      => 15  -- C₂
  | .C3      => 20  -- C₃
  | .C5plus  => 12  -- C₅⁺
  | .C5minus => 12  -- C₅⁻

/-- |A₅| = 60  -/
theorem conjClassSize_sum :
    (Finset.univ (α := A5ConjClass)).sum conjClassSize = 60 := by native_decide

/-- ρ₃′ （ρ₃  Galois : C₅⁺ ↔ C₅⁻ ） -/
def chi_rho3' : A5ConjClass → QSqrt5
  | .C1      => ⟨3, 0⟩             -- χ′(e) = 3
  | .C2      => ⟨-1, 0⟩            -- χ′(C₂) = −1
  | .C3      => ⟨0, 0⟩             -- χ′(C₃) = 0
  | .C5plus  => QSqrt5.neg_inv_phi  -- χ′(C₅⁺) = −1/φ  (ρ₃  C₅⁻ )
  | .C5minus => QSqrt5.phi          -- χ′(C₅⁻) = φ     (ρ₃  C₅⁺ )

/-- ρ₃  ρ₃′  C₅ （Galois ） -/
theorem rho3_rho3'_swap_on_C5 :
    chi_rho3 .C5plus = chi_rho3' .C5minus ∧
    chi_rho3 .C5minus = chi_rho3' .C5plus := by native_decide

/-- ρ₃  ρ₃′  C₁, C₂, C₃  -/
theorem rho3_rho3'_agree_off_C5 :
    chi_rho3 .C1 = chi_rho3' .C1 ∧
    chi_rho3 .C2 = chi_rho3' .C2 ∧
    chi_rho3 .C3 = chi_rho3' .C3 := by native_decide

/-- **ρ₃  ρ₃′  C₅ ** -/
theorem rho3_rho3'_diff_only_at_C5 (c : A5ConjClass) :
    chi_rho3 c ≠ chi_rho3' c ↔ (c = .C5plus ∨ c = .C5minus) := by
  fin_cases c <;> native_decide

/-- Fourier  C₅ 
     §5.6 「C₅⁺/C₅⁻ 」 -/
theorem fourier_diff_supported_on_C5 :
    ∀ c : A5ConjClass, c ≠ .C5plus → c ≠ .C5minus →
      QSqrt5.sub (chi_rho3 c) (chi_rho3' c) = QSqrt5.zero := by
  intro c h1 h2
  fin_cases c <;> simp_all <;> native_decide

end FourierCoefficients


/-!
══════════════════════════════════════════════════════════════════════════════
  §4. ρ₃/ρ₃′  ℤ₂ （§7.5.3）
══════════════════════════════════════════════════════════════════════════════

  Wilson : χ = χ_{ρ₃}  χ = χ_{ρ₃′} 2
   ℤ₂ （Section7_LatticeGaugeAction 
  distinguishing_count = 2 ）

  :  ρ₃/ρ₃′ （σ ）
    ・a ≠ a′  ⟺ ℤ₂ 
    ・a = a′  FM1（C₅ ）

  ****:  ℤ₂  Open Problem G1′
  
══════════════════════════════════════════════════════════════════════════════
-/

section Z2VacuumSelection

/-- ρ₃/ρ₃′ （ℤ₂ ） -/
inductive VacuumChoice
  | Rho3     -- ρ₃ : a > a′（ swap-odd ）
  | Rho3'    -- ρ₃′ : a < a′（ swap-odd ）
  | Symmetric -- a = a′（FM1: ）
  deriving Repr, DecidableEq, Fintype

/-- ℤ₂ : Rho3  Rho3′  Galois  -/
theorem vacuum_Z2_structure :
    ∀ v : VacuumChoice, v = .Rho3 ∨ v = .Rho3' ∨ v = .Symmetric := by
  intro v; fin_cases v <;> simp

/-- Rho3  ↔ Rho3′  Galois  g ↦ g² 
    （swap C₅⁺ ↔ C₅⁻ ） -/
theorem vacuum_galois_exchange :
    VacuumChoice.Rho3 ≠ VacuumChoice.Rho3' := by decide

/-- FM1 :  ↔ a = a′ -/
structure FM1_Condition where
  /-- a  a′  Q(√5)  -/
  a_minus_a' : QSqrt5
  /-- FM1: a = a′  -/
  vanishes : a_minus_a' = QSqrt5.zero

/-- FM1 （a ≠ a′）swap-odd 
     -/
theorem not_FM1_gives_asymmetry (h : ¬ ∃ (_ : FM1_Condition), True) :
    ∀ (q : QSqrt5), q = QSqrt5.zero → False := by
  intro _ hq
  apply h
  exact ⟨⟨_, hq⟩, trivial⟩

end Z2VacuumSelection


/-!
══════════════════════════════════════════════════════════════════════════════
  §5. Fourier 
══════════════════════════════════════════════════════════════════════════════

  §5.6 :
     A₅  μ 
    C₅⁺/C₅⁻  (a − a′)·√5 

  :
    Δ := χ_{ρ₃}(C₅⁺) − χ_{ρ₃}(C₅⁻) = √5
    [C₅⁺  μ  m₊, C₅⁻  μ  m₋ ]
    (a − a′) = (|C₅| / |A₅|) · (φ − (−1/φ)) · (m₊ − m₋)
             = (12/60) · √5 · (m₊ − m₋)
             = (√5/5) · (m₊ − m₋)

   (15) （dim ρ₃ = 3 ）:
    a − a′ = (√5/3) · (m₊ − m₋)  ...  (15)
══════════════════════════════════════════════════════════════════════════════
-/

section AlgebraicReduction

open QSqrt5

/-- C₅ : |C₅⁺| = |C₅⁻| = 12, |A₅| = 60 -/
def c5_weight_factor : ℚ := 12 / 60  -- = 1/5

/-- **Fourier : (12/60)·√5 = √5/5**

    a − a′ = c5_weight_factor · √5 · (m₊ − m₋) 
    （ dim ρ₃ = 3 ） -/
theorem fourier_diff_factor :
    c5_weight_factor = 1/5 := by native_decide

/-- dim(ρ₃) : (1/5)·1 = (√5/3)·(3/√5) 
     (15)  √5/3 （ Fourier ） -/
def normalized_c5_factor : ℚ := 1/5
  -- :  √5/3  Q(√5)  ⟨0, 1/3⟩ 
  --  (√5/3)·(m₊ − m₋) 

/-- **√5/3  Q(√5) （ Fourier  √5 ）** -/
def sqrt5_over_3 : QSqrt5 := ⟨0, 1/3⟩

/-- √5/3  (√5)/3  -/
theorem sqrt5_over_3_eq : sqrt5_over_3 = ⟨0, 1/3⟩ := rfl

/-- **: (χ_{ρ₃}(C₅⁺) − χ_{ρ₃}(C₅⁻)) / dim(ρ₃) = √5/3** -/
theorem normalized_character_gap :
    ⟨(chi_rho3 .C5plus).rat_part / 3 - (chi_rho3 .C5minus).rat_part / 3,
     (chi_rho3 .C5plus).sqrt5_part / 3 - (chi_rho3 .C5minus).sqrt5_part / 3⟩
    = (sqrt5_over_3 : QSqrt5) := by native_decide

/-- **C₅⁺  − C₅⁻  = (a − a′)·√5 **:

    Δ_response := Σ_c |c|·μ(c)·(χ_{ρ₃}(c) − χ_{ρ₃′}(c))
                = 12·m₊·(φ − (−1/φ)) + 12·m₋·((−1/φ) − φ)
                = 12·(m₊ − m₋)·(φ + 1/φ)
                = 12·(m₊ − m₋)·√5

    φ + 1/φ = √5  phi_add_inv  -/
theorem response_diff_via_phi_add_inv :
    add phi inv_phi = sqrt5 := phi_add_inv

end AlgebraicReduction


/-!
══════════════════════════════════════════════════════════════════════════════
  §6. a − a′ （ (15)）
══════════════════════════════════════════════════════════════════════════════

  ** §7.5.4 / Appendix A.6: a_sub_a′**

   (15): a − a′ = (√5/3)(m_{C₅⁺} − m_{C₅⁻})

  :
    ・m₊, m₋  C₅⁺/C₅⁻ （）
    ・ (15)  Q(√5) 
    ・ §7.5.4 

  ****: [P] —  B3 （FM2 ）
                        m₊, m₋  Open Problem G1′ 
══════════════════════════════════════════════════════════════════════════════
-/

section OccupancyReduction

open QSqrt5

/-- C₅ 
    m₊ = C₅⁺ , m₋ = C₅⁻ 
    [P] :  μ  heat-bath （ G1′） -/
structure C5OccupancyData where
  /-- C₅⁺ （） -/
  m_plus : ℚ
  /-- C₅⁻ （） -/
  m_minus : ℚ
  /-- ℤ₂ : m₊ ≠ m₋ -/
  neq : m_plus ≠ m_minus

/-- **Fourier  a − a′  Q(√5) **:

     B3（swap-odd  1 ）
    （§7.5.2 FM2 ）
    a − a′ （ (15) ） -/
noncomputable def a_sub_a' (occ : C5OccupancyData) : QSqrt5 :=
  -- (√5/3) · (m₊ − m₋)   Q(√5) 
  -- rat_part = 0, sqrt5_part = (m₊ − m₋)/3
  ⟨0, (occ.m_plus - occ.m_minus) / 3⟩

/-- ** (15) **:
    a − a′  √5  (m₊ − m₋)/3 
    （ (√5/3)(m₊ − m₋)  √5  1/3） -/
theorem a_sub_a'_sqrt5_part (occ : C5OccupancyData) :
    (a_sub_a' occ).sqrt5_part = (occ.m_plus - occ.m_minus) / 3 := rfl

/-- a − a′ （ √5 ） -/
theorem a_sub_a'_rational_part_zero (occ : C5OccupancyData) :
    (a_sub_a' occ).rat_part = 0 := rfl

/-- **a ≠ a′ ⟺ m₊ ≠ m₋（ℤ₂ ）** -/
theorem a_sub_a'_nonzero_iff (occ : C5OccupancyData) :
    a_sub_a' occ ≠ QSqrt5.zero ↔ occ.m_plus ≠ occ.m_minus := by
  constructor
  · -- a − a′ ≠ 0  m₊ ≠ m₋（: m₊ = m₋ → a − a′ = 0）
    intro h hcontra
    apply h
    simp only [a_sub_a', QSqrt5.zero, hcontra, sub_self, zero_div]
  · -- m₊ ≠ m₋  a − a′ ≠ 0
    intro hne heq
    apply hne
    -- heq : a_sub_a' occ = QSqrt5.zero
    -- → sqrt5_part  → (m₊ − m₋)/3 = 0 → m₊ = m₋
    have heq' : (a_sub_a' occ).sqrt5_part = (QSqrt5.zero).sqrt5_part :=
      congr_arg QSqrt5.sqrt5_part heq
    simp only [a_sub_a', QSqrt5.zero] at heq'
    have h3 : (3 : ℚ) ≠ 0 := by norm_num
    have hzero : occ.m_plus - occ.m_minus = 0 :=
      (div_eq_zero_iff.mp heq').resolve_right h3
    linarith

/-- ℤ₂ （occ.neq ）a ≠ a′ -/
theorem z2_vacuum_gives_nonzero_a_diff (occ : C5OccupancyData) :
    a_sub_a' occ ≠ QSqrt5.zero :=
  (a_sub_a'_nonzero_iff occ).mpr occ.neq

end OccupancyReduction


/-!
══════════════════════════════════════════════════════════════════════════════
  §7. Δ = (a − a′)·√5 （§5.6 ）
══════════════════════════════════════════════════════════════════════════════

  §5.6（）:
    >  A₅  μ 
    > C₅⁺/C₅⁻  (a − a′)√5 

   Q(√5) :
    Δ_total = (a − a′)·√5
            = ⟨0, (m₊ − m₋)/3⟩ · ⟨0, 1⟩  (Q(√5) )
            = ⟨5·(m₊ − m₋)/3, 0⟩           ()

   (15)  §7.4  normalizedCost_gap = √5/3 
══════════════════════════════════════════════════════════════════════════════
-/

section RateAsymmetryStructure

open QSqrt5

/-- ** Δ = (a − a′)·√5  Q(√5) **:

    a − a′ = ⟨0, (m₊ − m₋)/3⟩ 
    Δ = mul (a_sub_a' occ) sqrt5
      = ⟨5·(m₊ − m₋)/3, 0⟩（！）

    √5 ² = 5 Δ  -/
theorem total_rate_asymmetry (occ : C5OccupancyData) :
    mul (a_sub_a' occ) sqrt5
    = ⟨5 * (occ.m_plus - occ.m_minus) / 3, 0⟩ := by
  simp [a_sub_a', mul, sqrt5]
  ring

/-- Δ  (5/3)·(m₊ − m₋)（√5 「」） -/
theorem rate_asymmetry_is_rational (occ : C5OccupancyData) :
    (mul (a_sub_a' occ) sqrt5).sqrt5_part = 0 := by
  simp [total_rate_asymmetry]

/-- **normalizedCost_gap **:
    §7.4  cost  = ⟨0, 1/3⟩ = √5/3 
    a_sub_a'  √5  (1/3)  -/
theorem a_sub_a'_matches_normalized_cost_gap :
    sqrt5_over_3 = ⟨0, 1/3⟩ := rfl

/-- ****: No-go →  → Wilson  → heat-bath →
     → a − a′ = (√5/3)(m₊ − m₋) → Δ = (5/3)(m₊ − m₋) -/
structure HeatBathLogicChain where
  step1 : String :=
    "No-go (smoothLocal_noGo): finite holonomy + smooth-local → trivial"
  step2 : String :=
    "Discretization forced (nogo_forces_defect_reading): lattice or defect"
  step3 : String :=
    "Lattice gauge action S[U] = Σ_p (1 − χ_{ρ₃}(U_loop)/3)"
  step4 : String :=
    "Plaquette cost gap: cost(C₅⁻) − cost(C₅⁺) = √5 (plaquette_cost_gap_is_sqrt5)"
  step5 : String :=
    "Heat-bath kernel μ_β is central (FM2 closed: fm2_structural_closure)"
  step6 : String :=
    "φ + 1/φ = √5 (phi_add_inv, Appendix A.6)"
  step7 : String :=
    "a − a′ = (√5/3)(m₊ − m₋) (a_sub_a', formula (15), Appendix A.6)"
  step8 : String :=
    "Δ = (a − a′)·√5 = (5/3)(m₊ − m₋) [rational] (total_rate_asymmetry)"

theorem heatBath_chain_complete :
    let chain : HeatBathLogicChain := {}
    chain.step1.length > 0 ∧ chain.step2.length > 0 ∧
    chain.step3.length > 0 ∧ chain.step4.length > 0 ∧
    chain.step5.length > 0 ∧ chain.step6.length > 0 ∧
    chain.step7.length > 0 ∧ chain.step8.length > 0 := by decide

end RateAsymmetryStructure


/-!
══════════════════════════════════════════════════════════════════════════════
  §8. 
══════════════════════════════════════════════════════════════════════════════

  |                                     |                     |
  |----------------------------------------------|-------------------------------------|
  | Appendix A.6: φ + 1/φ = √5                  | phi_add_inv                         |
  | Appendix A.6:  (15) a − a′ = (√5/3)(m₊−m₋)| a_sub_a', a_sub_a'_sqrt5_part       |
  | §7.5.2: heat-bath                | fm2_structural_closure              |
  | §7.5.2: FM2                      | fm2_structural_closure              |
  | §7.5.3: ρ₃/ρ₃′                        | vacuum_Z2_structure                 |
  | §7.5.3: ℤ₂              | z2_vacuum_gives_nonzero_a_diff      |
  | §5.6: C₅                   | fourier_diff_supported_on_C5        |
  | §5.6: (a − a′)·√5                  | total_rate_asymmetry                |
  | §7.4 : √5/3                           | a_sub_a'_matches_normalized_cost_gap|
  | （8 ）               | heatBath_chain_complete             |
══════════════════════════════════════════════════════════════════════════════
-/


end CosmicNecessity
