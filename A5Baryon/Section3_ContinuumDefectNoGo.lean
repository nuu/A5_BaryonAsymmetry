/-
══════════════════════════════════════════════════════════════════════════════
  §3.1. Continuum vs Discreteness: Defect/Monodromy Reading (Lean Core)
══════════════════════════════════════════════════════════════════════════════

  File     : A5Baryon/Section3_ContinuumDefectNoGo.lean
  Paper    : §3.1 — No-go 「A」: / C₅ 
             （ 3.3 A ）
             "A No-Go Theorem for Smooth-Local Finite Holonomy and Its
             Discrete Implementations: Minimality of A₅ and an Application
             to the Baryogenesis Scale"
  Author   : M. Numagaki (Independent Researcher, Kumamoto, Japan)
  Date     : March 2026 (revised from February 2026)

  STATUS:  sorry = 0 | axiom = 0

  ──────────────────────────────────────────────────────────────────────
  :

    Section3_ContinuumNoGo.lean  No-go （ 3.2）:
      「smooth-local  +  = 」
    （ 3.3）
     No-go 「A」

     §3 （ 3.3）:
      A: （） →   ← 
               ρ : π₁(M \ Σ) → A₅
                Σ 
      B: （）                  ← Section4_LatticeGaugeAction.lean

    A :
      §1. DefectHolonomyModel — 
      §2. A5_IsConj （refl, symm, trans）
      §3. C₅⁺/C₅⁻  —  Galois swap (g ↦ g²)
      §4. 
      §5.  — defect 1
      §6. No-go → defect 

  ──────────────────────────────────────────────────────────────────────
  :

    : ConjugacyClassGalois.lean  (σ, σ², A5_IsConj, squaring maps)
            Section3_ContinuumNoGo.lean (MonodromyModel, FiniteHolonomyReading,
                                          3.2: smoothLocal_noGo,
                                          3.3: curvature_forces_not_local)
    : Section7_LatticeGaugeAction.lean（§7.4 ）
  ──────────────────────────────────────────────────────────────────────
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

import A5Baryon.ConjugacyClassGalois
import A5Baryon.Section3_ContinuumNoGo

set_option maxRecDepth 4000

namespace CosmicNecessity

open Classical


/-- A₅  -/
abbrev A5 : Type := alternatingGroup (Fin 5)


/-!
══════════════════════════════════════════════════════════════════════════════
  §1. DefectHolonomyModel — /
══════════════════════════════════════════════════════════════════════════════

  MonodromyModel（Loop + ρ ）:
    ・ Contractible  incl 
    ・ (ρ ∘ incl = 1) 
    ・ (∃ℓ, ρ ℓ ≠ 1) 

  :
    Loop        ↔ π₁(M \ Σ)       （）
    Contractible ↔       （）
    incl        ↔          （ ⊂ ）
    ρ           ↔    （ → A₅）
    local_trivial ↔    （No-go ）
    nontrivial_monodromy ↔ Σ 
-/

structure DefectHolonomyModel (H : Type*) [Group H] where
  Loop : Type*
  [instLoopGroup : Group Loop]
  Contractible : Type*
  [instContractibleGroup : Group Contractible]
  incl : Contractible →* Loop
  ρ : Loop →* H
  /-- :  -/
  local_trivial : ρ.comp incl = 1
  /-- :  -/
  nontrivial_monodromy : ∃ ℓ : Loop, ρ ℓ ≠ 1

attribute [instance] DefectHolonomyModel.instLoopGroup
attribute [instance] DefectHolonomyModel.instContractibleGroup


namespace DefectHolonomyModel

variable {H : Type*} [Group H]

/--  -/
theorem local_trivial_apply (D : DefectHolonomyModel H) (c : D.Contractible) :
    D.ρ (D.incl c) = 1 := by
  have h := congrArg (fun f => f c) D.local_trivial
  simpa using h

/--  ρ  -/
theorem rho_ne_one (D : DefectHolonomyModel H) : D.ρ ≠ 1 := by
  intro h
  rcases D.nontrivial_monodromy with ⟨ℓ, hℓ⟩
  have : D.ρ ℓ = 1 := by simpa [h]
  exact hℓ this

/--  ρ  -/
theorem finite_range_of_fintype (D : DefectHolonomyModel H) [Fintype H] :
    (Set.range D.ρ).Finite :=
  (Set.finite_univ : (Set.univ : Set H).Finite).subset (by intro x hx; trivial)

/-- ****: DefectHolonomyModel → MonodromyModel
    Contractible/incl/ MonodromyModel 
    FiniteHolonomyReading.defect  -/
def toMonodromyModel (D : DefectHolonomyModel H) : MonodromyModel H where
  Loop := D.Loop
  instLoopGroup := D.instLoopGroup
  ρ := D.ρ

end DefectHolonomyModel


/-!
══════════════════════════════════════════════════════════════════════════════
  §2.  A5_IsConj 
══════════════════════════════════════════════════════════════════════════════

  ConjugacyClassGalois.lean  A5_IsConj 
  （∃ k, k * g * k⁻¹ = h）
-/

namespace A5Conj

/--  -/
theorem refl (g : A5) : A5_IsConj g g :=
  ⟨1, by simp⟩

/--  -/
theorem symm {g h : A5} : A5_IsConj g h → A5_IsConj h g := by
  intro ⟨k, hk⟩
  exact ⟨k⁻¹, by calc
    k⁻¹ * h * (k⁻¹)⁻¹
        = k⁻¹ * (k * g * k⁻¹) * k := by simp [hk, mul_assoc]
    _ = g := by simp [mul_assoc]⟩

/--  -/
theorem trans {g h t : A5} : A5_IsConj g h → A5_IsConj h t → A5_IsConj g t := by
  intro ⟨k, hk⟩ ⟨m, hm⟩
  exact ⟨m * k, by calc
    (m * k) * g * (m * k)⁻¹
        = m * (k * g * k⁻¹) * m⁻¹ := by simp [mul_assoc]
    _ = m * h * m⁻¹ := by simp [hk, mul_assoc]
    _ = t := by simpa [hm, mul_assoc]⟩

/-- : g  a  b  a ~ b -/
theorem conj_of_conj_left {g a b : A5} :
    A5_IsConj g a → A5_IsConj g b → A5_IsConj a b := by
  intro ⟨k, hk⟩ ⟨m, hm⟩
  exact ⟨m * k⁻¹, by calc
    (m * k⁻¹) * a * (m * k⁻¹)⁻¹
        = (m * k⁻¹) * (k * g * k⁻¹) * (k * m⁻¹) := by simp [hk, mul_assoc]
    _ = m * g * m⁻¹ := by simp [mul_assoc]
    _ = b := by simpa [hm]⟩

end A5Conj


/-!
══════════════════════════════════════════════════════════════════════════════
  §3. C₅⁺/C₅⁻  —  Galois swap
══════════════════════════════════════════════════════════════════════════════

  ConjugacyClassGalois.lean  sigma_A5, sigma_sq_A5 
   g ↦ g²  C₅⁺ ↔ C₅⁻ （Galois ）
-/

/-- g  C₅⁺ （σ ） -/
def IsC5Plus (g : A5) : Prop := A5_IsConj g sigma_A5

/-- g  C₅⁻ （σ² ） -/
def IsC5Minus (g : A5) : Prop := A5_IsConj g sigma_sq_A5

/-- C₅⁺  C₅⁻ （σ  σ² ） -/
theorem C5Plus_disjoint_C5Minus (g : A5) : ¬ (IsC5Plus g ∧ IsC5Minus g) := by
  intro ⟨hplus, hminus⟩
  exact sigma_not_conj_sigma_sq (A5Conj.trans (A5Conj.symm hplus) hminus)

/--  C₅⁺  C₅⁻ （Galois swap ） -/
theorem sq_maps_plus_to_minus {g : A5} : IsC5Plus g → IsC5Minus (g ^ 2) :=
  squaring_maps_C5plus_to_C5minus g

/--  C₅⁻  C₅⁺ （Galois swap ） -/
theorem sq_maps_minus_to_plus {g : A5} : IsC5Minus g → IsC5Plus (g ^ 2) :=
  squaring_maps_C5minus_to_C5plus g


/-!
══════════════════════════════════════════════════════════════════════════════
  §4. 
══════════════════════════════════════════════════════════════════════════════

   Σ  ρ(ℓ)  C₅⁺ 
  g ↦ g²  C₅⁻ （）
-/

namespace DefectA5

variable (D : DefectHolonomyModel A5)

/--  C₅⁺  -/
def HitsC5Plus : Prop := ∃ ℓ : D.Loop, IsC5Plus (D.ρ ℓ)

/--  C₅⁻  -/
def HitsC5Minus : Prop := ∃ ℓ : D.Loop, IsC5Minus (D.ρ ℓ)

/-- C₅⁺  →  C₅⁻  -/
theorem hits_plus_implies_hits_minus_after_square :
    HitsC5Plus D → ∃ ℓ : D.Loop, IsC5Minus ((D.ρ ℓ) ^ 2) := by
  intro ⟨ℓ, hℓ⟩
  exact ⟨ℓ, sq_maps_plus_to_minus hℓ⟩

/-- C₅⁻  →  C₅⁺  -/
theorem hits_minus_implies_hits_plus_after_square :
    HitsC5Minus D → ∃ ℓ : D.Loop, IsC5Plus ((D.ρ ℓ) ^ 2) := by
  intro ⟨ℓ, hℓ⟩
  exact ⟨ℓ, sq_maps_minus_to_plus hℓ⟩

/-- ρ （A₅ ） -/
theorem finite_image : (Set.range D.ρ).Finite :=
  DefectHolonomyModel.finite_range_of_fintype D

end DefectA5


/-!
══════════════════════════════════════════════════════════════════════════════
  §5.  — Defect 1
══════════════════════════════════════════════════════════════════════════════
-/

theorem defect_reading_integrity
    (D : DefectHolonomyModel A5) :
    (∀ c : D.Contractible, D.ρ (D.incl c) = 1) ∧
    (D.ρ ≠ 1) ∧
    ((DefectA5.HitsC5Plus D) → ∃ ℓ : D.Loop, IsC5Minus ((D.ρ ℓ) ^ 2)) ∧
    ((DefectA5.HitsC5Minus D) → ∃ ℓ : D.Loop, IsC5Plus ((D.ρ ℓ) ^ 2)) ∧
    ((Set.range D.ρ).Finite) :=
  ⟨DefectHolonomyModel.local_trivial_apply D,
   DefectHolonomyModel.rho_ne_one D,
   DefectA5.hits_plus_implies_hits_minus_after_square D,
   DefectA5.hits_minus_implies_hits_plus_after_square D,
   DefectA5.finite_image D⟩


/-!
══════════════════════════════════════════════════════════════════════════════
  §6. No-go → Defect 
══════════════════════════════════════════════════════════════════════════════

  Phase 1–3 :
    (iii) +⇒ [TopologyFiniteConnected]
      → (v) smooth-local +  =  [Section3_ContinuumNoGo]
        → defect  []
          → C₅⁺/C₅⁻  [§3–§4]
-/

/-- DefectHolonomyModel  FiniteHolonomyReading.defect  -/
def DefectHolonomyModel.toFiniteHolonomyReading
    {K : Type*} [Group K] [TopologicalSpace K] [T1Space K]
    (D : DefectHolonomyModel K) :
    FiniteHolonomyReading K :=
  FiniteHolonomyReading.defect D.toMonodromyModel

/-- **No-go → Defect **:
    smooth-local  CurvNonzero 
    DefectHolonomyModel  FiniteHolonomyReading.defect  -/
theorem nogo_forces_defect_reading
    {K : Type*} [Group K] [TopologicalSpace K] [T1Space K]
    (M : SmoothLocalHolonomyModel K)
    (D : DefectHolonomyModel K) :
    (¬ M.CurvNonzero) ∧
    (D.toFiniteHolonomyReading = FiniteHolonomyReading.defect D.toMonodromyModel) :=
  ⟨smoothLocal_noGo M, rfl⟩


end CosmicNecessity
