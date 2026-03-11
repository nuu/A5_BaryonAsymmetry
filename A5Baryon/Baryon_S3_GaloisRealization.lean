/-
══════════════════════════════════════════════════════════════════════════════
  Baryon_S3_GaloisRealization.lean — §3 Claim 1: Galois 
  The Galois Realization Theorem: g ↦ g² exchanges C₅⁺ ↔ C₅⁻
══════════════════════════════════════════════════════════════════════════════

  File     : Baryon_S3_GaloisRealization.lean
  Paper    : "A No-Go Theorem for Smooth-Local Finite Holonomy and Its"
             "Discrete Implementations: Minimality of A₅ and an Application"
             "to the Baryogenesis Scale"
             §3 — Claim 1: Galois 
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  :

    Claim 1 [M]: Galois  g ↦ g² 52
    C₅⁺ ↔ C₅⁻  Δχ = √5 

     3.1（）:
      ∀ g ∈ A₅, ord(g) = 5 → g⁻¹ ∼_{A₅} g
      （）

     3.2（Galois ）:
      g ∈ C₅⁺ ⟹ g² ∈ C₅⁻
      g ∈ C₅⁻ ⟹ g² ∈ C₅⁺
      （2）

     3.3（）:
      |C₅⁺| = |C₅⁻| = 12
      （5 24）

  ──────────────────────────────────────────────────────────────────────
  :

    §3.4 — 5-cycle :

    (1) :
         Z_{S₅}(σ) = ⟨σ⟩ ⊂ A₅ 
        Z_{S₅}(σ) ∩ (S₅ \ A₅) = ∅ → 

    (2) :
        (ℤ/5ℤ)× = {1,2,3,4} :
          QR₅ = {1,4}（）→ C₅⁺
          NR₅ = {2,3}（）→ C₅⁻
        k ↦ 2k (mod 5)  QR₅ ↔ NR₅ 
        （2  mod 5 ）

    (3) :
        | g¹  | g²  | g³  | g⁴  | g⁵  |
        | C₅⁺ | C₅⁻ | C₅⁻ | C₅⁺ | {e} |

     √5:
      Δχ = |χ_{ρ₃}(C₅⁺) − χ_{ρ₃}(C₅⁻)| = |φ + 1/φ| = √5
       §5 Step 1  ηB 

  ──────────────────────────────────────────────────────────────────────
  ConjugacyClassGalois.lean :

     ConjugacyClassGalois.lean 
     §3 
     Claim 1 

    :
       3.1  →  inverse_preserves_conjugacy_class
       3.2  →  squaring_maps_C5plus_to_C5minus / _C5minus_to_C5plus
       3.3  →  C5_class_sizes
           →  galois_action_realization

  ──────────────────────────────────────────────────────────────────────
  :

     native_decide  A₅ 60
     Baryon_Common.lean 
     import 
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

namespace BaryonGaloisRealization

open Equiv Equiv.Perm


/-!
══════════════════════════════════════════════════════════════════════════════
  Foundations: ConjugacyClassGalois.lean 
══════════════════════════════════════════════════════════════════════════════

  
   import 
══════════════════════════════════════════════════════════════════════════════
-/

section Foundations

/-- 5 -/
@[reducible] def hasOrder5 (g : alternatingGroup (Fin 5)) : Prop := g ^ 5 = 1 ∧ g ≠ 1

/-- hasOrder5  orderOf = 5  -/
theorem hasOrder5_iff_orderOf (g : alternatingGroup (Fin 5)) :
    hasOrder5 g ↔ orderOf g = 5 := by
  constructor
  · intro ⟨h5, hne⟩
    have hdvd : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hne1 : orderOf g ≠ 1 := by
      intro h1; have := pow_orderOf_eq_one g
      rw [h1, pow_one] at this; exact hne this
    have hprime : Nat.Prime 5 := by norm_num
    rcases hprime.eq_one_or_self_of_dvd (orderOf g) hdvd with h | h
    · exact absurd h hne1
    · exact h
  · intro h5
    refine ⟨?_, ?_⟩
    · have := pow_orderOf_eq_one g; rwa [h5] at this
    · intro heq
      have h1 : orderOf g = 1 := by rw [heq]; exact orderOf_one
      omega

/-- 5-cycle σ = (01234) — C₅⁺  -/
def sigma_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1

def sigma_even : sigma_perm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

def sigma_A5 : alternatingGroup (Fin 5) := ⟨sigma_perm, sigma_even⟩

/-- σ² — C₅⁻  -/
def sigma_sq_A5 : alternatingGroup (Fin 5) := sigma_A5 ^ 2

/-- A₅  -/
def A5_IsConj (g h : alternatingGroup (Fin 5)) : Prop :=
  ∃ k : alternatingGroup (Fin 5), k * g * k⁻¹ = h

instance A5_IsConj_decidable (g h : alternatingGroup (Fin 5)) :
    Decidable (A5_IsConj g h) :=
  Fintype.decidableExistsFintype

end Foundations


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 1: §3.1 —  3.1（）
══════════════════════════════════════════════════════════════════════════════

   3.1（）:
     g ∈ A₅  ord(g) = 5 
    g⁻¹  A₅  g : g⁻¹ ∼_{A₅} g

  :
    g⁻¹ = g⁴ 4 ∈ QR₅ = {1,4}（4 = 2² ≡ 4 mod 5）
    g¹  g⁴ 
    

  Paper I :
    Paper I（§3.3） B(ℓ⁻¹) = −B(ℓ) 
     3.1  B(ℓ⁻¹) = B(ℓ)
══════════════════════════════════════════════════════════════════════════════
-/

section InversionPreservation

/--
  ** 3.1（ — hasOrder5 ）[M]**

  ∀ g ∈ A₅, hasOrder5 g → g ∼_{A₅} g⁻¹

  : A₅ 60（native_decide）
-/
theorem inverse_preserves_conjugacy_class' :
    ∀ g : alternatingGroup (Fin 5),
    hasOrder5 g → A5_IsConj g (g⁻¹) := by native_decide

/--
  ** 3.1（ — orderOf ）[M]**

  ∀ g ∈ A₅, orderOf g = 5 → g ∼_{A₅} g⁻¹

   §3.1  3.1 
-/
theorem inverse_preserves_conjugacy_class :
    ∀ g : alternatingGroup (Fin 5),
    orderOf g = 5 → A5_IsConj g (g⁻¹) := by
  intro g hord
  exact inverse_preserves_conjugacy_class' g ((hasOrder5_iff_orderOf g).mpr hord)

/--
  ** C₅⁺  [M]**

  g ∈ C₅⁺ ⟹ g⁻¹ ∈ C₅⁺

   3.1 「」
-/
theorem inversion_never_crosses :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 → A5_IsConj (g⁻¹) sigma_A5 := by native_decide

end InversionPreservation


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 2: §3.2 —  3.2（Galois ）
══════════════════════════════════════════════════════════════════════════════

   3.2（Galois ）:
     g ↦ g²  C₅⁺  C₅⁻ 

  :
    (ℤ/5ℤ)× 

    QR₅ = {1, 4}: 1² ≡ 1, 2² ≡ 4 (mod 5)
    NR₅ = {2, 3}: 

    σ = (01234) :
      C₅⁺ = { σᵏ : k ∈ QR₅ }  = {σ¹, σ⁴=σ⁻¹} 
      C₅⁻ = { σᵏ : k ∈ NR₅ }  = {σ², σ³=(σ²)⁻¹} 

     σᵏ ↦ σ²ᵏ  k ↦ 2k (mod 5)
    2 ∈ NR₅ :
      k ∈ QR₅ ⟹ 2k (mod 5) ∈ NR₅
      k ∈ NR₅ ⟹ 2k (mod 5) ∈ QR₅

     Galois 

  :
    Galois  σ_Gal: √5 ↦ −√5  φ ↦ −1/φ 
    ρ₃ ↔ ρ₃'  3.2  Galois 
    （group-theoretic realization）
══════════════════════════════════════════════════════════════════════════════
-/

section GaloisExchange

/--
  ** 3.2（→）: C₅⁺ → C₅⁻ [M]**

  g ∈ C₅⁺ ⟹ g² ∈ C₅⁻

   §3.2 
-/
theorem squaring_maps_C5plus_to_C5minus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5 := by native_decide

/--
  ** 3.2（←）: C₅⁻ → C₅⁺ [M]**

  g ∈ C₅⁻ ⟹ g² ∈ C₅⁺

   §3.2 
-/
theorem squaring_maps_C5minus_to_C5plus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5 := by native_decide

/--
  ** [M]**

  g ↦ g² 2 g⁴ = g⁻¹ ∼ g（ 3.1）
   (g²)²  g 

  : hasOrder5 g → g ∼_{A₅} (g²)²
-/
theorem squaring_involution :
    ∀ g : alternatingGroup (Fin 5),
    orderOf g = 5 → A5_IsConj g ((g ^ 2) ^ 2) := by
  intro g hord
  -- g⁴ = (g²)² and g⁴ = g⁻¹ ∼ g
  have : hasOrder5 g := (hasOrder5_iff_orderOf g).mpr hord
  show A5_IsConj g (g ^ 4)
  -- g⁴ = g⁻¹ in order 5 group, and g⁻¹ ∼ g
  have h_inv : A5_IsConj g (g⁻¹) := inverse_preserves_conjugacy_class g hord
  have h_pow4 : g⁻¹ = g ^ 4 := by
    have h5 : g ^ 5 = 1 := this.1
    have key : g ^ 4 * g = 1 := by
      have h := pow_add g 4 1
      rw [pow_one] at h
      rw [show (4 : ℕ) + 1 = 5 from rfl] at h
      rw [← h]; exact h5
    have h2 := inv_mul_cancel g
    exact (mul_right_cancel (key.trans h2.symm)).symm
  rwa [← h_pow4]

end GaloisExchange


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 3: §3.3 —  3.3（）
══════════════════════════════════════════════════════════════════════════════

   3.3（）:
    |C₅⁺| = |C₅⁻| = 12

  :
    |A₅| = 60, 5 = 24
    5212

    : |C₅⁺| = |A₅|/|Z_{A₅}(σ)| = 60/5 = 12
     ⟨σ⟩ ≅ ℤ₅ 5
══════════════════════════════════════════════════════════════════════════════
-/

section ClassSizes

/--
  ** 3.3: |C₅⁺| = |C₅⁻| = 12 [M]**

   §3.3
-/
theorem C5_class_sizes :
    (Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_A5 } = 12)
    ∧
    (Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_sq_A5 } = 12)
    := by constructor <;> native_decide

/--
  **5 = 24 [M]**

  |C₅⁺| + |C₅⁻| = 12 + 12 = 24
  A₅ 60524
-/
theorem order5_count :
    Fintype.card { g : alternatingGroup (Fin 5) // hasOrder5 g } = 24 := by
  native_decide

/--
  **C₅⁺  C₅⁻  [M]**

  σ  σ²  A₅ 
  S₅ A₅ 
-/
theorem C5_classes_distinct :
    ¬ A5_IsConj sigma_A5 sigma_sq_A5 := by native_decide

end ClassSizes


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 4: §3.4 — 
══════════════════════════════════════════════════════════════════════════════

  §3.4 
  （native_decide）
  「」

   Lean 
══════════════════════════════════════════════════════════════════════════════
-/

section ConceptualProof

/--
  ****

  (ℤ/5ℤ)× = {1, 2, 3, 4} /:
    QR₅ = {1, 4}（1² ≡ 1, 2² ≡ 4 mod 5）
    NR₅ = {2, 3}

  C₅⁺  QR₅ C₅⁻  NR₅ 
-/
structure QuadraticResidueClassification where
  /-- QR₅ = {1, 4}:  (mod 5) -/
  qr5_elements : List (ZMod 5) := [1, 4]
  /-- NR₅ = {2, 3}:  (mod 5) -/
  nr5_elements : List (ZMod 5) := [2, 3]
  /-- 2  mod 5  -/
  two_is_nonresidue : ¬ ∃ x : ZMod 5, x * x = 2

/-- **2  mod 5  [M]** -/
theorem two_is_qnr_mod5 : ¬ ∃ x : ZMod 5, x * x = 2 := by decide

/--
  ** [M]**

  g ∈ C₅⁺ :

    | g¹  | g²  | g³  | g⁴  | g⁵  |
    | C₅⁺ | C₅⁻ | C₅⁻ | C₅⁺ | {e} |

  g³ = (g²)⁻¹ ∈ C₅⁻（ + C₅⁻ ）
  g⁴ = g⁻¹ ∈ C₅⁺（ 3.1）
-/
theorem power_map_distribution_C5plus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 →
      -- g¹ ∈ C₅⁺
      A5_IsConj g sigma_A5
      ∧ -- g² ∈ C₅⁻
      A5_IsConj (g ^ 2) sigma_sq_A5
      ∧ -- g³ ∈ C₅⁻
      A5_IsConj (g ^ 3) sigma_sq_A5
      ∧ -- g⁴ ∈ C₅⁺
      A5_IsConj (g ^ 4) sigma_A5 := by native_decide

/--
  **（C₅⁻ ）[M]**

  g ∈ C₅⁻ :

    | g¹  | g²  | g³  | g⁴  | g⁵  |
    | C₅⁻ | C₅⁺ | C₅⁺ | C₅⁻ | {e} |
-/
theorem power_map_distribution_C5minus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_sq_A5 →
      A5_IsConj g sigma_sq_A5
      ∧ A5_IsConj (g ^ 2) sigma_A5
      ∧ A5_IsConj (g ^ 3) sigma_A5
      ∧ A5_IsConj (g ^ 4) sigma_sq_A5 := by native_decide

/--
  ** 2  QR₅ ↔ NR₅  [M]**

  k ↦ 2k (mod 5)  QR₅  NR₅ :
    2·1 ≡ 2 (mod 5): QR → NR
    2·4 ≡ 3 (mod 5): QR → NR
    2·2 ≡ 4 (mod 5): NR → QR
    2·3 ≡ 1 (mod 5): NR → QR
-/
theorem doubling_swaps_residue_classes :
    -- QR₅ 2 NR₅ 
    ((2 : ZMod 5) * 1 = 2 ∧ (2 : ZMod 5) * 4 = 3)
    ∧
    -- NR₅ 2 QR₅ 
    ((2 : ZMod 5) * 2 = 4 ∧ (2 : ZMod 5) * 3 = 1) := by decide

end ConceptualProof


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 5:  √5 
══════════════════════════════════════════════════════════════════════════════

  √5 
   √5 

   Δχ = |χ_{ρ₃}(C₅⁺) − χ_{ρ₃}(C₅⁻)| = |φ+1/φ| = √5

  :
    (i)   C₅⁺  C₅⁻  A₅ （C5_classes_distinct）
    (ii)  |C₅⁺| = |C₅⁻| = 12（C5_class_sizes）
    (iii) C₅⁺ ↔ C₅⁻  Out(A₅) （→ §4）

   Δχ ≠ 0 
  Δχ = √5 
══════════════════════════════════════════════════════════════════════════════
-/

section CharacterGapBasis

/--
  ** [M]**

  C₅⁺ ≇ C₅⁻ in A₅ |C₅⁺| = |C₅⁻| = 12
   S₅  A₅ 

   Δχ = √5 
  
-/
theorem character_gap_group_theoretic_basis :
    -- C₅⁺ ≇ C₅⁻
    ¬ A5_IsConj sigma_A5 sigma_sq_A5
    ∧
    -- |C₅⁺| = 12
    Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_A5 } = 12
    ∧
    -- |C₅⁻| = 12
    Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_sq_A5 } = 12
    ∧
    -- 5 = 24 = 12 + 12
    Fintype.card { g : alternatingGroup (Fin 5) // hasOrder5 g } = 24 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/--
  ** Q(√5) （）**

  A₅  Q(√5) Gal(Q(√5)/Q) ≅ ℤ₂ 
   √5 ↦ −√5  φ ↦ −1/φ 

  :
    ρ₃: χ(C₅⁺) = φ = (1+√5)/2,  χ(C₅⁻) = −1/φ = (1−√5)/2
    ρ₃': χ(C₅⁺) = −1/φ,          χ(C₅⁻) = φ

  :
    Δχ = |φ − (−1/φ)| = |φ + 1/φ| = |√5| = √5
    Σχ = φ + (−1/φ) = φ − 1/φ = 1

  :
    √5 
     Δχ 
    √5 = Δχ 
-/
structure CharacterGapRecord where
  /--  Q(√5) -/
  character_field : String := "Q(√5)"
  /-- ρ₃(C₅⁺) = φ -/
  rho3_C5plus : String := "φ = (1+√5)/2"
  /-- ρ₃(C₅⁻) = −1/φ -/
  rho3_C5minus : String := "−1/φ = (1−√5)/2"
  /-- Δχ = √5 -/
  character_gap : String := "√5"
  /-- Σχ = 1 -/
  character_sum : String := "1"

end CharacterGapBasis


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 6: Galois 
══════════════════════════════════════════════════════════════════════════════

  §3 

  Claim 1 4:
    (1) （ 3.1）
    (2) Galois  C₅⁺ → C₅⁻（ 3.2 ）
    (3) Galois  C₅⁻ → C₅⁺（ 3.2 ）
    (4)  |C₅⁺| = |C₅⁻| = 12（ 3.3）
══════════════════════════════════════════════════════════════════════════════
-/

section GaloisRealizationIntegration

/--
  **Claim 1 **

   §1 / §3 / §8  Claim 1 
-/
structure Claim1Complete where
  /--  3.1:  -/
  inverse_preserves :
    ∀ g : alternatingGroup (Fin 5),
    orderOf g = 5 → A5_IsConj g (g⁻¹)
  /--  3.2（→）: C₅⁺ → C₅⁻ -/
  squaring_plus_to_minus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5
  /--  3.2（←）: C₅⁻ → C₅⁺ -/
  squaring_minus_to_plus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5
  /--  3.3:  -/
  class_size_plus : Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_A5 } = 12
  class_size_minus : Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_sq_A5 } = 12

/--
  **Claim 1  [M]**

  Claim 1  sorry = 0, axiom = 0 

  : [M]（—）
-/
def claim1_complete : Claim1Complete :=
  { inverse_preserves := inverse_preserves_conjugacy_class
    squaring_plus_to_minus := squaring_maps_C5plus_to_C5minus
    squaring_minus_to_plus := squaring_maps_C5minus_to_C5plus
    class_size_plus := C5_class_sizes.1
    class_size_minus := C5_class_sizes.2 }

/--
  **Galois  [M]**

   §3 
  ConjugacyClassGalois.lean  galois_action_realization 
  C5_class_sizes 
-/
theorem galois_realization_theorem :
    --  3.1: 
    (∀ g : alternatingGroup (Fin 5),
     orderOf g = 5 → A5_IsConj g (g⁻¹))
    ∧
    --  3.2: Galois （）
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5)
    ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5)
    ∧
    --  3.3: 
    Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_A5 } = 12
    ∧
    Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_sq_A5 } = 12 :=
  ⟨inverse_preserves_conjugacy_class,
   squaring_maps_C5plus_to_C5minus,
   squaring_maps_C5minus_to_C5plus,
   C5_class_sizes.1,
   C5_class_sizes.2⟩

/--
  **Claim 1  [M]  [M]**

  Claim 1 
   (A1)–(A5) 
  : 
-/
theorem claim1_is_layer_M :
    -- 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5)
    ∧
    ¬ A5_IsConj sigma_A5 sigma_sq_A5 := by
  exact ⟨squaring_maps_C5plus_to_C5minus, C5_classes_distinct⟩

end GaloisRealizationIntegration


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 7: Paper I 
══════════════════════════════════════════════════════════════════════════════

  Paper I（§3.3） B(ℓ⁻¹) = −B(ℓ) 
   3.1  B(ℓ⁻¹) = B(ℓ)：
  

   3.1 
  
══════════════════════════════════════════════════════════════════════════════
-/

section PaperICorrection

/--
  Paper I  [M]

  B(ℓ⁻¹) = B(ℓ)（）
  : g⁻¹ ∼_{A₅} g
-/
theorem paper1_correction_basis :
    ∀ g : alternatingGroup (Fin 5),
    orderOf g = 5 → A5_IsConj g (g⁻¹) :=
  inverse_preserves_conjugacy_class

end PaperICorrection


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 8: 
══════════════════════════════════════════════════════════════════════════════
-/

section FileIntegrity

/--
  **§3  [M]**

   §3 
-/
theorem baryon_S3_file_integrity :
    --  3.1
    (∀ g : alternatingGroup (Fin 5),
     orderOf g = 5 → A5_IsConj g (g⁻¹))
    ∧
    --  3.2
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5)
    ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5)
    ∧
    --  3.3
    Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_A5 } = 12
    ∧
    Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_sq_A5 } = 12
    ∧
    -- 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 →
     A5_IsConj (g ^ 2) sigma_sq_A5 ∧
     A5_IsConj (g ^ 3) sigma_sq_A5 ∧
     A5_IsConj (g ^ 4) sigma_A5)
    ∧
    -- 
    ¬ ∃ x : ZMod 5, x * x = 2 :=
  ⟨inverse_preserves_conjugacy_class,
   squaring_maps_C5plus_to_C5minus,
   squaring_maps_C5minus_to_C5plus,
   C5_class_sizes.1,
   C5_class_sizes.2,
   fun g hg => let ⟨_, h2, h3, h4⟩ := power_map_distribution_C5plus g hg; ⟨h2, h3, h4⟩,
   two_is_qnr_mod5⟩

end FileIntegrity


/-!
══════════════════════════════════════════════════════════════════════════════
   §3 ↔ Lean 
══════════════════════════════════════════════════════════════════════════════

  | /                   | Lean                              |
  |---------------------------------|----------------------------------------|
  |  3.1                | inverse_preserves_conjugacy_class      |
  |  3.2 Galois  (→)        | squaring_maps_C5plus_to_C5minus        |
  |  3.2 Galois  (←)        | squaring_maps_C5minus_to_C5plus        |
  |  3.3            | C5_class_sizes                         |
  |  (C₅⁺ )            | power_map_distribution_C5plus          |
  |  (C₅⁻ )            | power_map_distribution_C5minus         |
  | 2  mod 5  QNR               | two_is_qnr_mod5                        |
  | 2k (mod 5)  QR/NR      | doubling_swaps_residue_classes         |
  | Galois                  | galois_realization_theorem              |
  | Claim 1                 | claim1_complete                         |
  |             | character_gap_group_theoretic_basis    |
  | Paper I                     | paper1_correction_basis                |
  |                   | baryon_S3_file_integrity               |

══════════════════════════════════════════════════════════════════════════════
-/


end BaryonGaloisRealization
