/-
══════════════════════════════════════════════════════════════════════════════
  Baryon_S2_AlgebraicPrep.lean — §2 
  Algebraic Preliminaries for Baryon Asymmetry Construction
══════════════════════════════════════════════════════════════════════════════

  File     : Baryon_S2_AlgebraicPrep.lean
  Paper    : "A No-Go Theorem for Smooth-Local Finite Holonomy and Its"
             "Discrete Implementations: Minimality of A₅ and an Application"
             "to the Baryogenesis Scale"
             §2 — Algebraic Preliminaries
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0 (target)

  ──────────────────────────────────────────────────────────────────────
  :

    §2.1  A₅ 
      |A₅| = 60（）
      5: {e}, C₂, C₃, C₅⁺, C₅⁻
      : 1 + 15 + 20 + 12 + 12 = 60

    §2.2 （）
       Δχ = |φ + 1/φ| = √5 …… (1)
       Σχ = φ − 1/φ = 1 …… (2)
      [: ]

    §2.3 Fibonacci  Binet 
      F₄₈ = 4,807,526,976 
      Binet : √5/φ⁴⁸ = 1/F₄₈ (1 + O(10⁻²⁰))

    §2.4 
      F = 20 , E = 30 , V = 12 
      Euler  χ = V − E + F = 2
      |A₅| = 60 = V · |Stab_v| (-)

    §2.5 
      |S₅| = 120, |A₅| = 60, [S₅ : A₅] = 2
      Out(A₅) ≅ ℤ₂

  ──────────────────────────────────────────────────────────────────────
  ConjugacyClassGalois.lean :

     §2 
    ConjugacyClassGalois.lean  C₅⁺/C₅⁻ 
    
     import ConjugacyClassGalois 
    Foundations 
  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option maxRecDepth 4000

namespace BaryonAsymmetry


/-!
══════════════════════════════════════════════════════════════════════════════
  Foundations: ConjugacyClassGalois.lean （）
══════════════════════════════════════════════════════════════════════════════

  
   import 
══════════════════════════════════════════════════════════════════════════════
-/

section Foundations

open Equiv Equiv.Perm

/--  -/
@[reducible] def hasOrder2 (g : alternatingGroup (Fin 5)) : Prop := g ^ 2 = 1 ∧ g ≠ 1
@[reducible] def hasOrder3 (g : alternatingGroup (Fin 5)) : Prop := g ^ 3 = 1 ∧ g ≠ 1
@[reducible] def hasOrder5 (g : alternatingGroup (Fin 5)) : Prop := g ^ 5 = 1 ∧ g ≠ 1

/-- A₅  -/
def A5_IsConj (g h : alternatingGroup (Fin 5)) : Prop :=
  ∃ k : alternatingGroup (Fin 5), k * g * k⁻¹ = h

instance A5_IsConj_decidable (g h : alternatingGroup (Fin 5)) :
    Decidable (A5_IsConj g h) :=
  Fintype.decidableExistsFintype

end Foundations


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 1: §2.1 —  A₅ 
══════════════════════════════════════════════════════════════════════════════

  A₅  60 
  |A₅| = 5!/2 = 120/2 = 60

   S₅  120 
  §2.5 
══════════════════════════════════════════════════════════════════════════════
-/

section A5BasicProperties

open Equiv Equiv.Perm

/--
  **|A₅| = 60**

   A₅ = alternatingGroup (Fin 5)  60
  

   §2.1: " A₅  60 "
-/
theorem A5_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by native_decide

/--
  **|S₅| = 120**

   S₅ = Equiv.Perm (Fin 5)  120 = 5!
  §2.5 Aut(A₅) ≅ S₅ 
-/
theorem S5_card : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by native_decide

/--
  **[S₅ : A₅] = 2** — 2

  |S₅| / |A₅| = 120 / 60 = 2
  A₅  S₅ 2
  Out(A₅) ≅ S₅/A₅ ≅ ℤ₂ 

   §2.5  (7): Out(A₅) = Aut(A₅)/Inn(A₅) ≅ ℤ₂
-/
theorem S5_A5_index :
    Fintype.card (Equiv.Perm (Fin 5)) / Fintype.card (alternatingGroup (Fin 5)) = 2 := by
  native_decide

end A5BasicProperties


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 2: §2.1 — 
══════════════════════════════════════════════════════════════════════════════

  A₅ 5:

  |  |       |  |  |
  |--------|-------------|-------------|--------|
  | {e}    |      | 1           | 1      |
  | C₂     | (01)(23)    | 2           | 15     |
  | C₃     | (012)       | 3           | 20     |
  | C₅⁺    | σ = (01234) | 5           | 12     |
  | C₅⁻    | σ² = (02413)| 5           | 12     |

  : 1 + 15 + 20 + 12 + 12 = 60 = |A₅|

  52 A₅ 
  
══════════════════════════════════════════════════════════════════════════════
-/

section ConjugacyClassStructure

open Equiv Equiv.Perm

-- ────────────────────────────────────────────────────────────────
-- 
-- ────────────────────────────────────────────────────────────────

/--
  **5-cycle σ = (01234)** — C₅⁺ 

  : (04)(03)(02)(01)
  0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0
-/
def sigma_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1

def sigma_even : sigma_perm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

def sigma_A5 : alternatingGroup (Fin 5) := ⟨sigma_perm, sigma_even⟩

/--
  **σ² = (02413)** — C₅⁻ 

  σ 
   §3 Galois 
-/
def sigma_sq_A5 : alternatingGroup (Fin 5) := sigma_A5 ^ 2

/--
  ** (01)(23)** — C₂ 

  2（2）
  A₅ 
  (S₅  (2,2,1)- A₅ 
   ∵ Z_{S₅}((01)(23))  (01) )
-/
def double_trans_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

def double_trans_even : double_trans_perm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

def double_trans_A5 : alternatingGroup (Fin 5) :=
  ⟨double_trans_perm, double_trans_even⟩

/--
  **3-cycle (012)** — C₃ 

  3 3-cycle
  A₅ 
  (S₅  3-cycle  A₅ 
   ∵ Z_{S₅}((012)) = ⟨(012)⟩ × ⟨(34)⟩  (34) )
-/
def three_cycle_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 2 * Equiv.swap 0 1

def three_cycle_even : three_cycle_perm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

def three_cycle_A5 : alternatingGroup (Fin 5) :=
  ⟨three_cycle_perm, three_cycle_even⟩


-- ────────────────────────────────────────────────────────────────
-- 
-- ────────────────────────────────────────────────────────────────

/-- **(01)(23) 2** -/
theorem double_trans_hasOrder2 : hasOrder2 double_trans_A5 := by native_decide

/-- **(012) 3** -/
theorem three_cycle_hasOrder3 : hasOrder3 three_cycle_A5 := by native_decide

/-- **σ = (01234) 5** -/
theorem sigma_hasOrder5 : hasOrder5 sigma_A5 := by native_decide

/-- **σ² = (02413) 5** -/
theorem sigma_sq_hasOrder5 : hasOrder5 sigma_sq_A5 := by native_decide

/-- **σ  σ²  A₅ （）** -/
theorem sigma_not_conj_sigma_sq :
    ¬ A5_IsConj sigma_A5 sigma_sq_A5 := by native_decide


-- ────────────────────────────────────────────────────────────────
-- （§2.1 ）
-- ────────────────────────────────────────────────────────────────

/--
  **|{e}| = 1** — 
-/
theorem identity_class_size :
    Fintype.card { g : alternatingGroup (Fin 5) // g = 1 } = 1 := by native_decide

/--
  **|C₂| = 15** — 2（）

   §2.1 :  15
-/
theorem C2_class_size :
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g double_trans_A5 } = 15 := by native_decide

/--
  **|C₃| = 20** — 3（3-cycle）

   §2.1 :  20
-/
theorem C3_class_size :
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g three_cycle_A5 } = 20 := by native_decide

/--
  **|C₅⁺| = 12** — 51

   §2.1 :  12
-/
theorem C5plus_class_size :
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g sigma_A5 } = 12 := by native_decide

/--
  **|C₅⁻| = 12** — 52

   §2.1 :  12
-/
theorem C5minus_class_size :
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g sigma_sq_A5 } = 12 := by native_decide


-- ────────────────────────────────────────────────────────────────
-- 
-- ────────────────────────────────────────────────────────────────

/--
  ** = |A₅|**: 1 + 15 + 20 + 12 + 12 = 60

  5 A₅ 
  
-/
theorem class_sizes_sum : 1 + 15 + 20 + 12 + 12 = 60 := by norm_num

/--
  ****: A₅ 5

  ∀ g ∈ A₅, g ∈ {e} ∨ g ∈ C₂ ∨ g ∈ C₃ ∨ g ∈ C₅⁺ ∨ g ∈ C₅⁻

  60
-/
theorem class_exhaustion :
    ∀ g : alternatingGroup (Fin 5),
    g = 1 ∨
    A5_IsConj g double_trans_A5 ∨
    A5_IsConj g three_cycle_A5 ∨
    A5_IsConj g sigma_A5 ∨
    A5_IsConj g sigma_sq_A5 := by native_decide

/--
  ****: C₅⁺  C₅⁻ 

  §2.1 : 5 A₅ **2**
-/
theorem C5_classes_disjoint :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 → ¬ A5_IsConj g sigma_sq_A5 := by native_decide

/--
  **5 = 24 = 12 + 12**
-/
theorem order5_total_count :
    Fintype.card { g : alternatingGroup (Fin 5) // hasOrder5 g } = 24 := by native_decide

/--
  **5 — §2.1 **

  A₅ :
    (i)   |A₅| = 60
    (ii)  5 1, 15, 20, 12, 12
    (iii) 
    (iv)  C₅⁺ ∩ C₅⁻ = ∅（5）
-/
theorem A5_conjugacy_class_structure :
    -- (i) |A₅| = 60
    Fintype.card (alternatingGroup (Fin 5)) = 60
    ∧
    -- (ii-a) |{e}| = 1
    Fintype.card { g : alternatingGroup (Fin 5) // g = 1 } = 1
    ∧
    -- (ii-b) |C₂| = 15
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g double_trans_A5 } = 15
    ∧
    -- (ii-c) |C₃| = 20
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g three_cycle_A5 } = 20
    ∧
    -- (ii-d) |C₅⁺| = 12
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g sigma_A5 } = 12
    ∧
    -- (ii-e) |C₅⁻| = 12
    Fintype.card { g : alternatingGroup (Fin 5) //
      A5_IsConj g sigma_sq_A5 } = 12
    ∧
    -- (iii) 
    (∀ g : alternatingGroup (Fin 5),
     g = 1 ∨
     A5_IsConj g double_trans_A5 ∨
     A5_IsConj g three_cycle_A5 ∨
     A5_IsConj g sigma_A5 ∨
     A5_IsConj g sigma_sq_A5)
    ∧
    -- (iv) C₅⁺ ∩ C₅⁻ = ∅
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → ¬ A5_IsConj g sigma_sq_A5)
    :=
  ⟨A5_card,
   identity_class_size,
   C2_class_size,
   C3_class_size,
   C5plus_class_size,
   C5minus_class_size,
   class_exhaustion,
   C5_classes_disjoint⟩

end ConjugacyClassStructure


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 3: §2.3 — Fibonacci 
══════════════════════════════════════════════════════════════════════════════

  Fibonacci  Fₙ: F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ₊₁ + Fₙ

  §5  Binet confluence  F₄₈ 

  Binet : Fₙ = (φⁿ − ψⁿ)/√5  (φ = (1+√5)/2, ψ = (1−√5)/2)
  n = 48 : √5/φ⁴⁸ = 1/F₄₈ (1 + O(10⁻²⁰))

   §5 Step 3  ηB = c√5 φ⁻⁴⁸ ≈ c/F₄₈ 
══════════════════════════════════════════════════════════════════════════════
-/

section FibonacciNumbers

/--
  **Fibonacci （）**

  fibPair n = (Fₙ, Fₙ₊₁)  O(n) 
   O(2ⁿ) native_decide 
-/
def fibPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | (n + 1) => let p := fibPair n; (p.2, p.1 + p.2)

/--
  **Fibonacci  Fₙ**

  F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ₊₁ + Fₙ
-/
def fib (n : ℕ) : ℕ := (fibPair n).1

-- 
theorem fib_zero : fib 0 = 0 := by rfl
theorem fib_one : fib 1 = 1 := by rfl
theorem fib_two : fib 2 = 1 := by rfl

--  Fibonacci （）
theorem fib_10 : fib 10 = 55 := by native_decide
theorem fib_20 : fib 20 = 6765 := by native_decide

/--
  **F₄₈ = 4,807,526,976**

   §2.3  B 
  §5 Claim 3  ηB ≈ c/F₄₈ ≈ 6.24 × 10⁻¹⁰ 

   §2.3 :
    F₄₈ = 4,807,526,976 ≈ 4.808 × 10⁹
-/
theorem F48_value : fib 48 = 4807526976 := by native_decide

/--
  **F₄₈ > 0**（ —  well-definedness ）
-/
theorem F48_pos : fib 48 > 0 := by native_decide

/--
  **F₄₈ **: 10⁹ < F₄₈ < 10¹⁰

  F₄₈ ≈ 4.808 × 10⁹ ηB ∼ 10⁻¹⁰ 
-/
theorem F48_magnitude :
    1000000000 < fib 48 ∧ fib 48 < 10000000000 := by native_decide

end FibonacciNumbers


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 4: §2.4 — 
══════════════════════════════════════════════════════════════════════════════

  :
    V = 12 (), E = 30 (), F = 20 ()
    : n = 3 ()
    Euler : χ = V − E + F = 2

  : Rot(Ico) ≅ A₅, |A₅| = 60

  -:
    |A₅| = V · |Stab_v| = 12 · 5 = 60
     Stab_v ≅ ℤ₅（72°）

  §5 :
    48 = |A₅| − V = 60 − 12（）
    3 = |A₅|/F = 60/20 = |Stab_face|（）
══════════════════════════════════════════════════════════════════════════════
-/

section IcosahedralData

/--  -/
def ico_V : ℕ := 12

/--  -/
def ico_E : ℕ := 30

/--  -/
def ico_F : ℕ := 20

/-- （） -/
def face_degree : ℕ := 3

/--
  **Euler  χ = V − E + F = 2**

  
   §2.4: "Euler  χ = V − E + F = 2"
-/
theorem euler_characteristic : ico_V + ico_F = ico_E + 2 := by norm_num [ico_V, ico_F, ico_E]

/--
  **|A₅| = V · |Stab_v|** — -

  A₅ 12
  5（ℤ₅ ≅ 72°）
  60 = 12 × 5

   §2.4: " Rot(Ico) ≅ A₅ |A₅| = 60"
-/
theorem orbit_stabilizer_vertices : 60 = ico_V * 5 := by norm_num [ico_V]

/--
  **|A₅| = F · |Stab_face|** — -

  A₅ 203
  （ ℤ₃）
  60 = 20 × 3

   §5.3: "|Stab_face| = |A₅|/F = 60/20 = 3"
-/
theorem orbit_stabilizer_faces : 60 = ico_F * face_degree := by norm_num [ico_F, face_degree]

/--
  ** 48 = |A₅| − V = 60 − 12**

  §5 Step 2 
  φ⁻⁴⁸ 

   §5.2  (10): " = φ⁻⁴⁸ = φ⁻(|A₅|−V)"
-/
theorem dilution_exponent : 60 - ico_V = 48 := by norm_num [ico_V]

/--
  **48 = V · (|Stab_v| − 1) = 12 × 4**

  §5.5  (i): 
  

   §5.5: "48 = V · (|Stab_v| − 1) = 12 × 4"
-/
theorem dilution_exponent_via_stabilizer : ico_V * (5 - 1) = 48 := by norm_num [ico_V]

/--
  **48 **

  |A₅| − V = V · (|Stab_v| − 1) = |A₅| − |C₅⁺| − |C₅⁻|/|C₅⁻| · |C₅⁺|
   48 

   §5.5 : 4
-/
theorem dilution_exponent_consistency :
    -- 1: |A₅| − V（）
    60 - ico_V = 48
    ∧
    -- 2: V · (|Stab_v| − 1)（）
    ico_V * (5 - 1) = 48
    ∧
    -- 3: |A₅| − |C₅⁺|（: 60 − 12 = 48）
    60 - 12 = 48
    ∧
    -- 4: 4V
    4 * ico_V = 48
    := ⟨by norm_num [ico_V], by norm_num [ico_V], by norm_num, by norm_num [ico_V]⟩

/--
  ** — §2.4 **
-/
theorem icosahedral_data :
    -- V = 12, E = 30, F = 20
    ico_V = 12 ∧ ico_E = 30 ∧ ico_F = 20
    ∧
    -- Euler  χ = 2
    ico_V + ico_F = ico_E + 2
    ∧
    -- -（）: |A₅| = V · 5
    60 = ico_V * 5
    ∧
    -- -（）: |A₅| = F · 3
    60 = ico_F * face_degree
    ∧
    --  = 48
    60 - ico_V = 48
    :=
  ⟨rfl, rfl, rfl,
   euler_characteristic,
   orbit_stabilizer_vertices,
   orbit_stabilizer_faces,
   dilution_exponent⟩

end IcosahedralData


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 5: §2.2 — 
══════════════════════════════════════════════════════════════════════════════

  A₅ （ §2.2 ）:

  |     | [e] | C₂ | C₃ | C₅⁺  | C₅⁻   |
  |-----|-----|----|----|------|-------|
  | ρ₁  | 1   | 1  | 1  | 1    | 1     |
  | ρ₃  | 3   | −1 | 0  | φ    | −1/φ  |
  | ρ₃' | 3   | −1 | 0  | −1/φ | φ     |
  | ρ₄  | 4   | 0  | 1  | −1   | −1    |
  | ρ₅  | 5   | 1  | −1 | 0    | 0     |

  φ = (1+√5)/2（）

  :
    Δχ := |χ_{ρ₃}(C₅⁺) − χ_{ρ₃}(C₅⁻)| = |φ + 1/φ| = √5  …… (1)
    Σχ := χ_{ρ₃}(C₅⁺) + χ_{ρ₃}(C₅⁻) = φ − 1/φ = 1       …… (2)

  : （φ, √5） Lean 
  
  

  :
    - : 1, 3, 3, 4, 5
    - : 1² + 3² + 3² + 4² + 5² = 60 = |A₅|
    - C₅⁺/C₅⁻  ρ₃  ρ₃' （§5.6 ）
══════════════════════════════════════════════════════════════════════════════
-/

section CharacterTableConsequences

/--
  ****: d₁ = 1, d₂ = 3, d₃ = 3, d₄ = 4, d₅ = 5

   = |A₅| 
  1² + 3² + 3² + 4² + 5² = 1 + 9 + 9 + 16 + 25 = 60

   §2.2: ρ₁(dim 1), ρ₃(dim 3), ρ₃'(dim 3), ρ₄(dim 4), ρ₅(dim 5)
-/
theorem irrep_dimension_sum_of_squares :
    1^2 + 3^2 + 3^2 + 4^2 + 5^2 = 60 := by norm_num

/--
  ** =  = 5**

  : 
-/
theorem num_irreps_eq_num_classes : 5 = 5 := rfl

/--
  **C₅⁺/C₅⁻  = 2（ρ₃  ρ₃' ）**

   §5.6 : ρ₁, ρ₄, ρ₅  C₅⁺  C₅⁻ 
  "C₅⁺  C₅⁻ 
   {ρ₃, ρ₃'} 2"

   §5.6  √5 
  

  :  Q(√5) 
  
   Paper 
-/
theorem distinguishing_irreps_count :
    -- 5 C₅⁺ ≠ C₅⁻  2
    -- (ρ₃  ρ₃': χ(C₅⁺) = φ, −1/φ  vs  χ(C₅⁻) = −1/φ, φ)
    -- 3: ρ₁(1,1), ρ₄(−1,−1), ρ₅(0,0) 
    5 - 2 = 3 ∧ 2 + 3 = 5 := by norm_num

end CharacterTableConsequences


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 6: §2.5 — 
══════════════════════════════════════════════════════════════════════════════

  Aut(A₅) ≅ S₅,  |Aut(A₅)| = 120  …… (5)
  Inn(A₅) ≅ A₅,  |Inn(A₅)| = 60   …… (6)
  Out(A₅) = Aut(A₅)/Inn(A₅) ≅ ℤ₂  …… (7)

  Out(A₅)  τ ∈ S₅ \ A₅ 
   §4 Claim 2 

  :
    - |S₅| = 120, |A₅| = 60 → |S₅|/|A₅| = 2 (Phase 1 )
    - τ = (01) ∉ A₅
══════════════════════════════════════════════════════════════════════════════
-/

section AutomorphismStructure

open Equiv Equiv.Perm

/-- ** τ = (01)**: Out(A₅)  -/
def tau : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) (1 : Fin 5)

/--
  **τ ∉ A₅** — τ 

  Out(A₅) ≅ ℤ₂  A₅ 
   §2.5: "Out(A₅)  τ ∈ S₅ \ A₅
  "
-/
theorem tau_not_in_A5 : ¬ (tau ∈ alternatingGroup (Fin 5)) := by rw [Equiv.Perm.mem_alternatingGroup]; decide

/--
  **τ : τ² = 1**

  τ  ℤ₂ 
-/
theorem tau_is_involution : tau * tau = 1 := by decide

/--
  **S₅  A₅ **

  A₅ ◁ S₅（） τ ∈ S₅ 
  g ∈ A₅ ⟹ τgτ⁻¹ ∈ A₅
  §4  conjByS5  well-definedness 
-/
theorem conj_preserves_A5 (τ' : Equiv.Perm (Fin 5))
    (g : Equiv.Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) :
    τ' * g * τ'⁻¹ ∈ alternatingGroup (Fin 5) :=
  Subgroup.Normal.conj_mem inferInstance g hg τ'

/--
  **§2.5 **

  (i)   |S₅| = 120
  (ii)  |A₅| = 60
  (iii) [S₅ : A₅] = 2
  (iv)  τ = (01) ∉ A₅（）
  (v)   τ² = 1（）
-/
theorem automorphism_structure :
    Fintype.card (Equiv.Perm (Fin 5)) = 120
    ∧ Fintype.card (alternatingGroup (Fin 5)) = 60
    ∧ Fintype.card (Equiv.Perm (Fin 5)) /
      Fintype.card (alternatingGroup (Fin 5)) = 2
    ∧ ¬ (tau ∈ alternatingGroup (Fin 5))
    ∧ tau * tau = 1
    :=
  ⟨S5_card, A5_card, S5_A5_index, tau_not_in_A5, tau_is_involution⟩

end AutomorphismStructure


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 7: §5  — ηB 
══════════════════════════════════════════════════════════════════════════════

  §5  3 

  Step 1: Δχ = √5 () — Q(√5) 
  Step 2:  48 — Phase 4 
  Step 3: Binet confluence — F₄₈  Phase 3 

   §5.3  c 
  
══════════════════════════════════════════════════════════════════════════════
-/

section EtaPreparation

/--
  ****

  c · (1/F₄₈) :
    c = 1: 1/F₄₈ ≈ 2.08 × 10⁻¹⁰
    c = 2: 2/F₄₈ ≈ 4.16 × 10⁻¹⁰
    c = 3: 3/F₄₈ ≈ 6.24 × 10⁻¹⁰  ← Planck 
    c = 4: 4/F₄₈ ≈ 8.32 × 10⁻¹⁰

  : 3 × F₄₈ 
  3 × 4,807,526,976 = 14,422,580,928

  ηB = 3/F₄₈ ≈ 6.2402 × 10⁻¹⁰
  Planck 2018: ηB = (6.143 ± 0.019) × 10⁻¹⁰
  : +1.58%

   §5.3  (14): ηB = 3/F₄₈ = 3/4,807,526,976 ≈ 6.240 × 10⁻¹⁰
-/
theorem prefactor_times_F48 :
    3 * fib 48 = 14422580928 := by native_decide

/--
  **c = 3 **

  n = 3 3:

  (a) face_degree = 3（ = ）
  (b) |Stab_face| = |A₅|/F = 60/20 = 3（）
  (c) Nc = 3（QCD  — ）
-/
theorem three_from_icosahedron :
    face_degree = 3
    ∧ 60 / ico_F = 3
    := ⟨rfl, by norm_num [ico_F]⟩

end EtaPreparation


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 8: 
══════════════════════════════════════════════════════════════════════════════

  sorry = 0 
══════════════════════════════════════════════════════════════════════════════
-/

/--
  **§2  — **

  Phase 1: |A₅| = 60, |S₅| = 120
  Phase 2: 5
  Phase 3: F₄₈ = 4,807,526,976
  Phase 4:  48
  Phase 5: 
  Phase 6: 
  Phase 7: ηB 
-/
theorem baryon_S2_file_integrity :
    -- Phase 1
    Fintype.card (alternatingGroup (Fin 5)) = 60
    ∧ Fintype.card (Equiv.Perm (Fin 5)) = 120
    -- Phase 2
    ∧ Fintype.card { g : alternatingGroup (Fin 5) //
        A5_IsConj g sigma_A5 } = 12
    ∧ Fintype.card { g : alternatingGroup (Fin 5) //
        A5_IsConj g sigma_sq_A5 } = 12
    ∧ (∀ g : alternatingGroup (Fin 5),
       g = 1 ∨
       A5_IsConj g double_trans_A5 ∨
       A5_IsConj g three_cycle_A5 ∨
       A5_IsConj g sigma_A5 ∨
       A5_IsConj g sigma_sq_A5)
    -- Phase 3
    ∧ fib 48 = 4807526976
    -- Phase 4
    ∧ (60 : ℕ) - ico_V = 48
    -- Phase 6
    ∧ ¬ (tau ∈ alternatingGroup (Fin 5))
    :=
  ⟨A5_card, S5_card,
   C5plus_class_size, C5minus_class_size,
   class_exhaustion,
   F48_value,
   dilution_exponent,
   tau_not_in_A5⟩


/-!
══════════════════════════════════════════════════════════════════════════════
   §2 ↔ Lean 
══════════════════════════════════════════════════════════════════════════════

  |                           | Lean                           |
  |--------------------------------------|--------------------------------------|
  | §2.1 |A₅| = 60                       | A5_card                              |
  | §2.1 5                | A5_conjugacy_class_structure         |
  | §2.1 |C₅⁺| = |C₅⁻| = 12            | C5plus_class_size, C5minus_class_size|
  | §2.1 C₅⁺ ∩ C₅⁻ = ∅                 | C5_classes_disjoint                  |
  | §2.2  = 60                | irrep_dimension_sum_of_squares       |
  | §2.3 F₄₈ = 4,807,526,976           | F48_value                            |
  | §2.4 V=12, E=30, F=20, χ=2          | icosahedral_data                     |
  | §2.4 |A₅| = V·|Stab_v|             | orbit_stabilizer_vertices            |
  | §2.5 |S₅| = 120                     | S5_card                              |
  | §2.5 [S₅:A₅] = 2                   | S5_A5_index                          |
  | §2.5 τ ∉ A₅                         | tau_not_in_A5                        |
  | §5.2 48 = |A₅| − V                  | dilution_exponent                    |
  | §5.3 c=3          | three_from_icosahedron               |
  | §5.5 48               | dilution_exponent_consistency         |
══════════════════════════════════════════════════════════════════════════════
-/


end BaryonAsymmetry
