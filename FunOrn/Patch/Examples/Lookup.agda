module FunOrn.Patch.Examples.Lookup 
         (A : Set)
       where

open import FunOrn.Functions.Examples.Le
open import FunOrn.FunOrnament.Examples.Lookup

open import FunOrn.FunOrnament
open import FunOrn.Patch

open import Data.Unit
open import Logic.Logic

-- Paper: Example 5.16
typeILookup : Set
typeILookup = Patch _<_ (typeLookup A)

