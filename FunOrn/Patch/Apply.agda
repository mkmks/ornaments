module FunOrn.Patch.Apply where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.Fixpoint

open import Orn.Ornament
open import Orn.Ornament.Algebra 
open import Orn.Reornament
open import Orn.Reornament.Make
open import Orn.Reornament.Algebra

open import FunOrn.Functions
open import FunOrn.FunOrnament
open import FunOrn.Patch

-- Paper: Definition 5.22
patch : ∀ {I I⁺ : Set}{u : I⁺ → I}{i⁺ : I⁺}
        {T : type I} → (fo : forn T u)(f : ⟦ T ⟧type (u i⁺)) →
        Patch f (forn.out fo i⁺) → ⟦ fo ⟧Forn i⁺
patch {I}{I⁺}{u}{i⁺}{T} fo f p = go (forn.out fo i⁺) f p where
  go : ∀ {U : Type} → (fo : FunctionOrn U) → (f : ⟦ U ⟧Type) →
     Patch {U} f fo → ⟦ fo ⟧FunctionOrn
  go (μ⁺ o [ inv i⁺ ]→ U⁺) f p = λ x → go U⁺ (f (forget o x)) (p (forget o x) (make o x))
  go (μ⁺ o [ inv i⁺ ]× U⁺) (x , xs) (x⁺⁺ , p) = forgetReornament o x⁺⁺ , go U⁺ xs p
  go `⊤ _ _ = tt
