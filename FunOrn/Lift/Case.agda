

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Case
         {I I⁺ : Set }
         {D : func  I I}
         {u : I⁺ → I}
         (o : orn D u u)
       where

open import Data.Product

open import Logic.Logic 

open import IDesc.Fixpoint
open import IDesc.Case

open import Orn.Reornament

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

liftCases : ∀ {T : type I} → Cases D (λ {i} _ → ⟦ T ⟧type i) → forn T u → Set 
liftCases α T⁺ = Cases ⌈ o ⌉D 
                       (λ {ix} xs → Patch (case D _ α (proj₂ ix)) (forn.out T⁺ (proj₁ ix)))

-- Paper: Definition 6.8
lift-case : {i⁺ : I⁺}{T : type I}{T⁺ : forn T u}
           (α : Cases D (λ {i} _ → ⟦ T ⟧type i))
           (β : liftCases α T⁺)  →
    Patch
      (case D (λ {i} _ → ⟦ T ⟧type i) α) (μ⁺ o [ inv i⁺ ]→ forn.out T⁺ i⁺)
lift-case α β = 
  λ x x⁺⁺ → case ⌈ o ⌉D _  (λ {i} xs → β {i} xs) x⁺⁺
