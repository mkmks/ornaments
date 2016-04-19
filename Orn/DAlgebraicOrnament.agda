open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Binary.PropositionalEquality

open import Logic.Logic

open import IDesc.IDesc
open import IDesc.Fixpoint
open import IDesc.InitialAlgebra
open import IDesc.Induction
open import IDesc.Lifting renaming ( □h to □hd )

open import Orn.Ornament
open import Orn.Ornament.Examples.DLifting renaming ( □h to □ho )

module Orn.DAlgebraicOrnament
           {K : Set }
           {D : func K K}
           {P : {i : K} → μ D i → Set} where

I : Set 
I = Σ K (λ k → Σ (μ D k) P)

u : I → K
u = proj₁

module Desc
         (k : K)
         (xs : ⟦ D ⟧func (μ D) k)
         (x : P ⟨ xs ⟩)
         (α : DAlg D P) where

  dalgOrn : Orn u (func.out D k)
  dalgOrn = insert (α (Induction.hyps D P α (func.out D k) xs) ≡ x) λ _ →
            □ho {L = K}{ind = induction D P α} (func.out D k) xs

  dalgOrnD : IDesc I
  dalgOrnD = ⟦ dalgOrn ⟧Orn

module Func (α : DAlg D P) where

  algOrn : orn D u u
  algOrn = orn.mk (λ { (k , ⟨ xs ⟩ , x) → Desc.dalgOrn k xs x α })

  -- Paper: Section 4.4
  -- Typeset: algOrnD D α = D^α
  algOrnD : func  I I
  algOrnD = ⟦ algOrn ⟧orn

open Func public

