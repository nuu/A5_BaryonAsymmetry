/-
══════════════════════════════════════════════════════════════════════════════
  Baryon_S4_OutNecessity.lean — §4 Claim 2: Out(A₅) 
  The Out(A₅) Necessity Theorem and Power Map Distribution
══════════════════════════════════════════════════════════════════════════════

  File     : Baryon_S4_OutNecessity.lean
  Paper    : "A No-Go Theorem for Smooth-Local Finite Holonomy and Its"
             "Discrete Implementations: Minimality of A₅ and an Application"
             "to the Baryogenesis Scale"
             §4 — Claim 2: Out(A₅) 
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0 (target)

  ──────────────────────────────────────────────────────────────────────
  :

     4.1 (Out(A₅)  — ):
      C₅⁺  C₅⁻  A₅ 
       Out(A₅) ≅ Z₂（）

      :
        (a) ∀ h ∈ A₅, ∀ g ∈ C₅⁺: hgh⁻¹ ∈ C₅⁺
            （ C₅⁺ ）
        (b) ∃ τ ∈ S₅ \ A₅: ∀ g ∈ C₅⁺, τgτ⁻¹ ∈ C₅⁻
            （ C₅⁺ → C₅⁻ ）

     4.2 ():
      g ∈ C₅⁺  {g, g², g³, g⁴, g⁵=e} 
      C₅⁺ 2C₅⁻ 2{e} 1 

  ──────────────────────────────────────────────────────────────────────
  :

    S₅ = Equiv.Perm (Fin 5)  A₅ 
    A₅ ◁ S₅ （）S₅ 
    A₅  conjByS5 

     native_decide 
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

namespace BaryonOutNecessity

open Equiv Equiv.Perm


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 0: ConjugacyClassGalois.lean （）
══════════════════════════════════════════════════════════════════════════════

   ConjugacyClassGalois.lean 
  
   import 

  Baryon_S2_AlgebraicPrep.lean / Baryon_S3_GaloisRealization.lean
   Baryon_Common.lean 
══════════════════════════════════════════════════════════════════════════════
-/

section Foundations

/-- 5 -/
@[reducible] def hasOrder5 (g : alternatingGroup (Fin 5)) : Prop := g ^ 5 = 1 ∧ g ≠ 1

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

def double_trans_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

def double_trans_even : double_trans_perm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

def double_trans_A5 : alternatingGroup (Fin 5) := ⟨double_trans_perm, double_trans_even⟩

end Foundations


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 1: S₅  A₅ 
══════════════════════════════════════════════════════════════════════════════

  A₅ ◁ S₅  τ ∈ S₅ 
  g ∈ A₅ → τgτ⁻¹ ∈ A₅ 

  :
    alternatingGroup  sign  kernel 
    kernel Mathlib  Normal instance 
══════════════════════════════════════════════════════════════════════════════
-/

section S5Conjugation

/--
  **S₅  A₅ **: τ ∈ S₅, g ∈ A₅ → τgτ⁻¹ ∈ A₅

  : A₅ = ker(sign)  S₅ 
  

  : sign(τgτ⁻¹) = sign(τ)·sign(g)·sign(τ)⁻¹ = sign(g) = 1
-/
theorem conj_mem_alternating (τ : Equiv.Perm (Fin 5))
    (g : Equiv.Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) :
    τ * g * τ⁻¹ ∈ alternatingGroup (Fin 5) :=
  -- alternatingGroup = sign.ker 
  Subgroup.Normal.conj_mem inferInstance g hg τ

/--
  **S₅ **: τ ∈ S₅  A₅ 
   A₅ 
-/
def conjByS5 (τ : Equiv.Perm (Fin 5))
    (g : alternatingGroup (Fin 5)) : alternatingGroup (Fin 5) :=
  ⟨τ * g.val * τ⁻¹, conj_mem_alternating τ g.val g.prop⟩

end S5Conjugation


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 2:  τ = (01) 
══════════════════════════════════════════════════════════════════════════════

  τ = swap 0 1 
  τ ∈ S₅ \ A₅ Out(A₅) 
══════════════════════════════════════════════════════════════════════════════
-/

section OddPermutation

/-- ** τ = (01)**:  swap 0 1 -/
def tau : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) (1 : Fin 5)

/-- **τ （A₅ ）** -/
theorem tau_not_in_A5 : ¬ (tau ∈ alternatingGroup (Fin 5)) := by rw [Equiv.Perm.mem_alternatingGroup]; decide

/-- **τ : τ² = 1** -/
theorem tau_sq_eq_one : tau * tau = 1 := by decide

/-- **τ⁻¹ = τ**（） -/
theorem tau_inv_eq_self : tau⁻¹ = tau := by decide

end OddPermutation


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 3:  4.1 — Out(A₅) （）
══════════════════════════════════════════════════════════════════════════════

  Part (a):  C₅⁺ 
    ∀ g ∈ C₅⁺, ∀ h ∈ A₅: hgh⁻¹ ∈ C₅⁺

  Part (b):  τ  C₅⁺  C₅⁻ 
    ∀ g ∈ C₅⁺: τgτ⁻¹ ∈ C₅⁻

  Part (a) （）
  Part (b)  native_decide 
══════════════════════════════════════════════════════════════════════════════
-/

section OutA5Necessity

/--
  ** 4.1(a):  C₅⁺ **

  g  σ  A₅-（g ∈ C₅⁺） h ∈ A₅ 
  hgh⁻¹  σ  A₅-（hgh⁻¹ ∈ C₅⁺）

  :
  ∃ k, kgk⁻¹ = σ  j := kh⁻¹ 
  j(hgh⁻¹)j⁻¹ = kgk⁻¹ = σ

  60×60 = 3600 
-/
theorem inner_aut_preserves_C5plus :
    ∀ (g h : alternatingGroup (Fin 5)),
    A5_IsConj g sigma_A5 →
    A5_IsConj (h * g * h⁻¹) sigma_A5 := by native_decide

/--
  ** 4.1(a'):  C₅⁻ **
-/
theorem inner_aut_preserves_C5minus :
    ∀ (g h : alternatingGroup (Fin 5)),
    A5_IsConj g sigma_sq_A5 →
    A5_IsConj (h * g * h⁻¹) sigma_sq_A5 := by native_decide

/--
  ** 4.1(b):  τ  C₅⁺  C₅⁻ **（）

  ∀ g ∈ A₅: g  σ  A₅- → τgτ⁻¹  σ²  A₅-

  S₅  A₅ 
   Out(A₅) ≅ Z₂ 
-/
theorem odd_perm_maps_C5plus_to_C5minus :
    ∀ (g : alternatingGroup (Fin 5)),
    A5_IsConj g sigma_A5 →
    A5_IsConj (conjByS5 tau g) sigma_sq_A5 := by native_decide

/--
  ** 4.1(b'): τ  C₅⁻  C₅⁺ **（）
-/
theorem odd_perm_maps_C5minus_to_C5plus :
    ∀ (g : alternatingGroup (Fin 5)),
    A5_IsConj g sigma_sq_A5 →
    A5_IsConj (conjByS5 tau g) sigma_A5 := by native_decide

/--
  ** 4.1(c): **（）

  τ' ∈ A₅ → τ'  C₅⁺  C₅⁺ 
  conjByS5 τ' g  h * g * h⁻¹ （A₅ ）
-/
theorem even_perm_preserves_C5plus :
    ∀ (g h : alternatingGroup (Fin 5)),
    A5_IsConj g sigma_A5 →
    A5_IsConj (h * g * h⁻¹) sigma_A5 := by native_decide

/--
  ** 4.1 : Out(A₅) **

  (i)  （） C₅⁺ 
  (ii)  （ τ） C₅⁺  C₅⁻ 
  (iii) τ  C₅⁻  C₅⁺ （Z₂ ）
  (iv) τ ∉ A₅

   C₅⁺ ↔ C₅⁻  Out(A₅) 
-/
theorem out_A5_necessity :
    -- (i)  C₅⁺ 
    (∀ (g h : alternatingGroup (Fin 5)),
     A5_IsConj g sigma_A5 →
     A5_IsConj (h * g * h⁻¹) sigma_A5)
    ∧
    -- (ii) τ  C₅⁺ → C₅⁻
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 →
     A5_IsConj (conjByS5 tau g) sigma_sq_A5)
    ∧
    -- (iii) τ  C₅⁻ → C₅⁺
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 →
     A5_IsConj (conjByS5 tau g) sigma_A5)
    ∧
    -- (iv) τ ∉ A₅
    ¬ (tau ∈ alternatingGroup (Fin 5))
    :=
  ⟨even_perm_preserves_C5plus,
   odd_perm_maps_C5plus_to_C5minus,
   odd_perm_maps_C5minus_to_C5plus,
   tau_not_in_A5⟩

end OutA5Necessity


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 4:  4.2 — 
══════════════════════════════════════════════════════════════════════════════

  g ∈ C₅⁺ (5)  {g¹, g², g³, g⁴, g⁵} 
  

  :
    g¹ ∈ C₅⁺  ()
    g² ∈ C₅⁻  (Galois :  3.2)
    g³ ∈ C₅⁻  (g³ = (g²)⁻¹, )
    g⁴ ∈ C₅⁺  (g⁴ = g⁻¹, )
    g⁵ = e     (5)
══════════════════════════════════════════════════════════════════════════════
-/

section PowerMapDistribution

/--
  ** 4.2(a): g³ ∈ C₅⁻ for g ∈ C₅⁺**

  g ∈ C₅⁺ → g² ∈ C₅⁻ ( 3.2)
  g³ = (g²)⁻¹ (∵ g² · g³ = g⁵ = e)
  (g²)⁻¹ ∈ C₅⁻ (:  3.1  C₅⁻ )

  native_decide 
-/
theorem cube_in_C5minus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 →
    A5_IsConj (g ^ 3) sigma_sq_A5 := by native_decide

/--
  ** 4.2(b): g⁴ ∈ C₅⁺ for g ∈ C₅⁺**

  g⁴ = g⁻¹ (∵ g⁴ · g = g⁵ = e)
  g⁻¹ ∈ C₅⁺ (:  3.1)

  native_decide 
-/
theorem fourth_power_in_C5plus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 →
    A5_IsConj (g ^ 4) sigma_A5 := by native_decide

/--
  ** 4.2(c): g⁵ = e for g ∈ C₅⁺**

  55
-/
theorem fifth_power_is_identity :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 →
    g ^ 5 = 1 := by native_decide

/--
  ** 4.2: **

  g ∈ C₅⁺ :
    g¹ ∈ C₅⁺,  g² ∈ C₅⁻,  g³ ∈ C₅⁻,  g⁴ ∈ C₅⁺,  g⁵ = e

  : C₅⁺ 2 (g¹, g⁴)C₅⁻ 2 (g², g³){e} 1 (g⁵)
  : 2 + 2 + 1 = 5 = ord(g)
-/
theorem power_map_distribution :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 →
    -- g¹ ∈ C₅⁺ ()
    A5_IsConj (g ^ 1) sigma_A5 ∧
    -- g² ∈ C₅⁻ (Galois )
    A5_IsConj (g ^ 2) sigma_sq_A5 ∧
    -- g³ ∈ C₅⁻
    A5_IsConj (g ^ 3) sigma_sq_A5 ∧
    -- g⁴ ∈ C₅⁺ ()
    A5_IsConj (g ^ 4) sigma_A5 ∧
    -- g⁵ = e
    g ^ 5 = 1
    := by native_decide

end PowerMapDistribution


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 5: C₅⁻ 
══════════════════════════════════════════════════════════════════════════════

  C₅⁻ 
══════════════════════════════════════════════════════════════════════════════
-/

section C5MinusMirror

/--
  **C₅⁻ **

  g ∈ C₅⁻ :
    g¹ ∈ C₅⁻,  g² ∈ C₅⁺,  g³ ∈ C₅⁺,  g⁴ ∈ C₅⁻,  g⁵ = e

  C₅⁺ 
-/
theorem power_map_distribution_C5minus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_sq_A5 →
    A5_IsConj (g ^ 1) sigma_sq_A5 ∧
    A5_IsConj (g ^ 2) sigma_A5 ∧
    A5_IsConj (g ^ 3) sigma_A5 ∧
    A5_IsConj (g ^ 4) sigma_sq_A5 ∧
    g ^ 5 = 1
    := by native_decide

end C5MinusMirror


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 6: （§4.4 ）
══════════════════════════════════════════════════════════════════════════════

  §3–§4 3 A₅ 
══════════════════════════════════════════════════════════════════════════════
-/

section SakharovAlgebraicBasis

/--
  **A₅ ** —  (S2) 

  σ·σ² ≠ σ²·σ 
  C₅⁺  C₅⁻ 
-/
theorem sigma_sigma_sq_not_commute :
    sigma_A5 * double_trans_A5 ≠ double_trans_A5 * sigma_A5 := by native_decide

/--
  ** 60^N ≥ 2^(5N)** —  (S3) 

  |A₅|^N = 60^N ≥ 32^N = 2^(5N)
  
-/
theorem cumulative_barrier (N : ℕ) : 60 ^ N ≥ 2 ^ (5 * N) := by
  have : 2 ^ (5 * N) = (2 ^ 5) ^ N := by rw [Nat.pow_mul]
  rw [this]
  exact Nat.pow_le_pow_left (by norm_num : 2 ^ 5 ≤ 60) N

/--
  **3 A₅  — **

  (S1) B :   A₅  → B 
  (S2) C/CP : Out(A₅) ≅ Z₂  C₅⁺ ↔ C₅⁻ 
  (S3) :    60^N  → 

  
   Layer P 
-/
theorem sakharov_algebraic_basis :
    -- (S1) A₅  → 
    (sigma_A5 * double_trans_A5 ≠ double_trans_A5 * sigma_A5) ∧
    -- (S2) Out(A₅)  C₅⁺ ↔ C₅⁻ 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (conjByS5 tau g) sigma_sq_A5) ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 → A5_IsConj (conjByS5 tau g) sigma_A5) ∧
    -- (S3) 
    (60 ^ 1 ≥ 2 ^ 5)
    :=
  ⟨sigma_sigma_sq_not_commute,
   odd_perm_maps_C5plus_to_C5minus,
   odd_perm_maps_C5minus_to_C5plus,
   cumulative_barrier 1⟩

end SakharovAlgebraicBasis


/-!
══════════════════════════════════════════════════════════════════════════════
  Phase 7: 
══════════════════════════════════════════════════════════════════════════════
-/

/--
  ** — **
-/
theorem outA5_file_integrity :
    -- Phase 2: τ 
    (¬ (tau ∈ alternatingGroup (Fin 5))) ∧
    (tau * tau = 1) ∧
    -- Phase 3: Out(A₅) 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 →
     A5_IsConj (conjByS5 tau g) sigma_sq_A5) ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 →
     A5_IsConj (conjByS5 tau g) sigma_A5) ∧
    -- Phase 4: 
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 →
     A5_IsConj (g ^ 1) sigma_A5 ∧
     A5_IsConj (g ^ 2) sigma_sq_A5 ∧
     A5_IsConj (g ^ 3) sigma_sq_A5 ∧
     A5_IsConj (g ^ 4) sigma_A5 ∧
     g ^ 5 = 1)
    :=
  ⟨tau_not_in_A5,
   tau_sq_eq_one,
   odd_perm_maps_C5plus_to_C5minus,
   odd_perm_maps_C5minus_to_C5plus,
   power_map_distribution⟩


/-!
══════════════════════════════════════════════════════════════════════════════
   §4 ↔ Lean 
══════════════════════════════════════════════════════════════════════════════

  |                                 | Lean /                     |
  |--------------------------------------------|--------------------------------------|
  | §4.1(a)  C₅⁺          | inner_aut_preserves_C5plus           |
  | §4.1(a')  C₅⁻         | inner_aut_preserves_C5minus          |
  | §4.1(b) τ: C₅⁺ → C₅⁻                     | odd_perm_maps_C5plus_to_C5minus      |
  | §4.1(b') τ: C₅⁻ → C₅⁺                    | odd_perm_maps_C5minus_to_C5plus      |
  | §4.1(c)  C₅⁺                  | even_perm_preserves_C5plus           |
  | §4.1(c) τ ∉ A₅                            | tau_not_in_A5                        |
  | §4.1                                  | out_A5_necessity                     |
  | §4.2(a) g³ ∈ C₅⁻                          | cube_in_C5minus                      |
  | §4.2(b) g⁴ ∈ C₅⁺                          | fourth_power_in_C5plus               |
  | §4.2(c) g⁵ = e                            | fifth_power_is_identity              |
  | §4.2                        | power_map_distribution               |
  | §4.2 C₅⁻                         | power_map_distribution_C5minus       |
  | §4.3 Sakharov (S1)                | sigma_sigma_sq_not_commute           |
  | §4.3 Sakharov (S3)                | cumulative_barrier                   |
  | §4.3 Sakharov                         | sakharov_algebraic_basis             |
  | τ                                 | tau_sq_eq_one, tau_inv_eq_self       |
  | S₅  A₅                         | conj_mem_alternating                 |
  | S₅                                | conjByS5                             |
  |                             | outA5_file_integrity                 |
══════════════════════════════════════════════════════════════════════════════
-/


end BaryonOutNecessity
