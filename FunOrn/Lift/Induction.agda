

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Induction
         {I I⁺ : Set }
         {D : func  I I}
         {u : I⁺ → I}
         (o : orn D u u)
       where

open import Data.Product

open import Logic.Logic 

open import IDesc.Fixpoint
open import IDesc.Induction

open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

-- Paper: Definition 6.6
liftIH : {T : type I} → DAlg D (λ {i} _ → ⟦ T ⟧type i) →
  forn T u → Set 
liftIH {T} α T⁺ = DAlg ⌈ o ⌉D ((λ {ix} _ →
  Patch (induction D _ α (proj₂ ix)) (forn.out T⁺ (proj₁ ix))))

-- Paper: Definition 6.7
lift-ind : {i⁺ : I⁺}{T : type I }{T⁺ : forn T u}
          (α : DAlg D (λ {i} _ → ⟦ T ⟧type i))
          (β : liftIH α T⁺) →
    Patch
      (induction D (λ {i} _ → ⟦ T ⟧type i) α)
      (μ⁺ o [ inv i⁺ ]→ forn.out T⁺ i⁺)
lift-ind α β = λ x x⁺⁺ → induction ⌈ o ⌉D _ (λ {ix} → β {ix}) x⁺⁺
