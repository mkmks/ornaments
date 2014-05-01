

open import IDesc.IDesc

open import Orn.Ornament

module FunOrn.Lift.Constructor
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
open import FunOrn.Lift.MkReorn o

-- Paper: Definition 6.17
lift-constructor : {i⁺ : I⁺}
                  {T : type I}{T⁺ : forn T u}
                  {t : ⟦ T ⟧type (u i⁺)} →
                  {x : ⟦ D ⟧func (μ D) (u i⁺)}
                  (e : Extra {i⁺ = inv i⁺} x) → Args {i⁺ = inv i⁺} x e →
                  Patch t (forn.out T⁺ i⁺) →
                  Patch (⟨ x ⟩ , t) (μ⁺ o [ inv i⁺ ]× forn.out T⁺ i⁺)
lift-constructor e a p = mkreorn e a , p
