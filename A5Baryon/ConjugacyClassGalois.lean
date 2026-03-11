/-
══════════════════════════════════════════════════════════════════════════════
  ConjugacyClassGalois.lean
  Conjugacy Class Structure and Galois Action on C₅ Classes in A₅
══════════════════════════════════════════════════════════════════════════════

  File     : A5CosmicNecessity/ConjugacyClassGalois.lean
  Author   : Masaru Numagaki
  Date     : February 2026

  STATUS:  sorry = 0 | axiom = 0

══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option maxRecDepth 4000

namespace CosmicNecessity

open Equiv Equiv.Perm



@[reducible] def hasOrder5 (g : alternatingGroup (Fin 5)) : Prop := g ^ 5 = 1 ∧ g ≠ 1

theorem hasOrder5_iff_orderOf (g : alternatingGroup (Fin 5)) :
    hasOrder5 g ↔ orderOf g = 5 := by
  constructor
  ·
    intro ⟨h5, hne⟩
    have hdvd : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hne1 : orderOf g ≠ 1 := by
      intro h1
      have := pow_orderOf_eq_one g
      rw [h1, pow_one] at this
      exact hne this
    have hprime : Nat.Prime 5 := by norm_num
    rcases hprime.eq_one_or_self_of_dvd (orderOf g) hdvd with h | h
    · exact absurd h hne1
    · exact h
  ·
    intro h5
    constructor
    · have h := pow_orderOf_eq_one g  -- g ^ (orderOf g) = 1
      rw [h5] at h                     -- g ^ 5 = 1
      exact h
    · intro heq
      have h1 : orderOf g = 1 := by rw [heq]; exact orderOf_one
      omega



section ConcreteElements

def sigma_perm : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 4 * Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1

theorem sigma_even : sigma_perm ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

def sigma_A5 : alternatingGroup (Fin 5) := ⟨sigma_perm, sigma_even⟩

theorem sigma_hasOrder5 : hasOrder5 sigma_A5 := by native_decide

theorem sigma_order : orderOf sigma_A5 = 5 :=
  (hasOrder5_iff_orderOf sigma_A5).mp sigma_hasOrder5

def sigma_sq_A5 : alternatingGroup (Fin 5) := sigma_A5 ^ 2

theorem sigma_sq_hasOrder5 : hasOrder5 sigma_sq_A5 := by native_decide

theorem sigma_sq_order : orderOf sigma_sq_A5 = 5 :=
  (hasOrder5_iff_orderOf sigma_sq_A5).mp sigma_sq_hasOrder5

theorem sigma_sq_ne_sigma : sigma_sq_A5 ≠ sigma_A5 := by native_decide

theorem sigma_inv_eq_pow4 : sigma_A5⁻¹ = sigma_A5 ^ 4 := by native_decide

end ConcreteElements


section ConjugacyClasses

def A5_IsConj (g h : alternatingGroup (Fin 5)) : Prop :=
  ∃ k : alternatingGroup (Fin 5), k * g * k⁻¹ = h

instance A5_IsConj_decidable (g h : alternatingGroup (Fin 5)) :
    Decidable (A5_IsConj g h) :=
  Fintype.decidableExistsFintype

theorem sigma_not_conj_sigma_sq :
    ¬ A5_IsConj sigma_A5 sigma_sq_A5 := by native_decide

theorem sigma_conj_sigma_inv :
    A5_IsConj sigma_A5 (sigma_A5⁻¹) := by native_decide

theorem sigma_sq_conj_sigma_sq_inv :
    A5_IsConj sigma_sq_A5 (sigma_sq_A5⁻¹) := by native_decide

end ConjugacyClasses


section MainTheorems

theorem inverse_preserves_conjugacy_class' :
    ∀ g : alternatingGroup (Fin 5),
    hasOrder5 g → A5_IsConj g (g⁻¹) := by native_decide

theorem inverse_preserves_conjugacy_class :
    ∀ g : alternatingGroup (Fin 5),
    orderOf g = 5 → A5_IsConj g (g⁻¹) := by
  intro g hord
  exact inverse_preserves_conjugacy_class' g ((hasOrder5_iff_orderOf g).mpr hord)

theorem squaring_maps_C5plus_to_C5minus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5 := by native_decide

theorem squaring_maps_C5minus_to_C5plus :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5 := by native_decide

theorem squaring_involution' :
    ∀ g : alternatingGroup (Fin 5),
    hasOrder5 g → A5_IsConj g ((g ^ 2) ^ 2) := by native_decide

theorem squaring_involution :
    ∀ g : alternatingGroup (Fin 5),
    orderOf g = 5 → A5_IsConj g ((g ^ 2) ^ 2) := by
  intro g hord
  exact squaring_involution' g ((hasOrder5_iff_orderOf g).mpr hord)

end MainTheorems


section GaloisRealization

theorem galois_action_realization :
    (∀ g : alternatingGroup (Fin 5),
     orderOf g = 5 → A5_IsConj g (g⁻¹))
    ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5)
    ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5)
    := ⟨inverse_preserves_conjugacy_class,
        squaring_maps_C5plus_to_C5minus,
        squaring_maps_C5minus_to_C5plus⟩

theorem C5_class_sizes :
    (Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_A5 } = 12)
    ∧
    (Fintype.card { g : alternatingGroup (Fin 5) // A5_IsConj g sigma_sq_A5 } = 12)
    := by constructor <;> native_decide

theorem order5_count :
    Fintype.card { g : alternatingGroup (Fin 5) // hasOrder5 g } = 24 := by
  native_decide

theorem inversion_never_crosses :
    ∀ g : alternatingGroup (Fin 5),
    A5_IsConj g sigma_A5 → A5_IsConj (g⁻¹) sigma_A5 := by native_decide

end GaloisRealization


theorem file_integrity_check :
    (orderOf sigma_A5 = 5) ∧
    (orderOf sigma_sq_A5 = 5) ∧
    (sigma_sq_A5 ≠ sigma_A5) ∧
    (¬ A5_IsConj sigma_A5 sigma_sq_A5) ∧
    (A5_IsConj sigma_A5 (sigma_A5⁻¹)) ∧
    (∀ g : alternatingGroup (Fin 5),
     orderOf g = 5 → A5_IsConj g (g⁻¹)) ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_A5 → A5_IsConj (g ^ 2) sigma_sq_A5) ∧
    (∀ g : alternatingGroup (Fin 5),
     A5_IsConj g sigma_sq_A5 → A5_IsConj (g ^ 2) sigma_A5)
    :=
  ⟨sigma_order, sigma_sq_order, sigma_sq_ne_sigma,
   sigma_not_conj_sigma_sq, sigma_conj_sigma_inv,
   inverse_preserves_conjugacy_class,
   squaring_maps_C5plus_to_C5minus,
   squaring_maps_C5minus_to_C5plus⟩


end CosmicNecessity
