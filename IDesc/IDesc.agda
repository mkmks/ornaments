module IDesc.IDesc where

open import Data.Unit 
open import Data.Nat hiding (_⊔_)
open import Data.Fin hiding (lift)
open import Data.Product 
open import Function

open import Logic.Logic

infixr 30 _`×_

-- Paper: Definition 3.2
data IDesc (I : Set) : Set₁ where
  `var : (i : I) → IDesc I
  `1 : IDesc I
  `Σ : (S : Set )(T : S → IDesc I) → IDesc I
  `Π : (S : Set )(T : S → IDesc I) → IDesc I
  -- Redundant (but first-order) connectives:
  _`×_ : (A B : IDesc I) → IDesc I
  `σ : (n : ℕ)(T : Fin n → IDesc I) → IDesc I

-- Paper: Definition 3.2
⟦_⟧ : {I : Set} → IDesc I → (I → Set) → Set
⟦ `var i ⟧ X = X i
⟦ `1 ⟧ X = ⊤
⟦ A `× B ⟧ X = ⟦ A ⟧ X × ⟦ B ⟧ X
⟦ `σ n T ⟧ X = Σ[ k ∈ Fin n ] ⟦ T k ⟧ X
⟦ `Σ S T ⟧ X = Σ[ s ∈ S ] ⟦ T s ⟧ X
⟦ `Π S T ⟧ X = (s : S) → ⟦ T s ⟧ X

-- Paper typesetting: ⟦_⟧^{→}
⟦_⟧map : ∀{ I X Y} → (D : IDesc  I) → (f : X ⇒ Y) →  ⟦ D ⟧ X → ⟦ D ⟧ Y
⟦ `var i ⟧map f xs = f xs
⟦ `1 ⟧map f tt = tt
⟦ A `× B ⟧map f (a , b) = ⟦ A ⟧map f a , ⟦ B ⟧map f b
⟦ `σ n T ⟧map f (k , xs) = k , ⟦ T k ⟧map f xs
⟦ `Σ S T ⟧map f (s , xs) = s , ⟦ T s ⟧map f xs
⟦ `Π S T ⟧map f xs = λ s → ⟦ T s ⟧map f (xs s)

{-
This definition does not play well with unification:

func : (I J : Set) → Set₁
func I J = J → IDesc I

Instead, we sugar it in a record, as follows:
-}

-- Paper: Definition 3.3
record func (I J : Set) : Set₁ where
  constructor mk
  field
    out : J → IDesc I

-- Paper: Definition 3.3
-- Paper typesetting: ⟦_⟧
⟦_⟧func : {I J : Set} → func  I J → (I → Set) → (J → Set)
⟦ D ⟧func X j = ⟦ func.out D j ⟧ X 

-- Paper: Definition 3.3
-- Paper typesetting: ⟦_⟧^{→}
⟦_⟧fmap : ∀{ I J X Y} → (D : func I J) → (f : X ⇒ Y) →  ⟦ D ⟧func X ⇒ ⟦ D ⟧func Y
⟦ D ⟧fmap f {j} xs = ⟦ func.out D j ⟧map f xs

_◎'_ : ∀ {I J} → IDesc J → (J → IDesc I) → IDesc I
`var j ◎' G = G j
`1 ◎' G = `1
`Σ S T ◎' G = `Σ S λ s → T s ◎' G
`Π S T ◎' G = `Π S λ s → T s ◎' G
(F'₁ `× F'₂) ◎' G = (F'₁ ◎' G) `× (F'₂ ◎' G)
`σ n T ◎' G = `σ n λ s → T s ◎' G

infixl 20 _◎'_

_◎_ : ∀ {I J K} → func J K → func I J → func I K
_◎_ {I}{J}{K} (mk F) (mk G) = mk λ k → F k ◎' G

infixl 20 _◎_

◎'-assoc' : ∀ {I J}{F G H}{X : I → Set} → ⟦ F ◎' func.out (mk G ◎ mk H) ⟧ X → ⟦ _◎'_ {J = J} (_◎'_ {J = J} F G) H ⟧ X 
◎'-assoc' {F = `var _} = id
◎'-assoc' {F = `1} = id
◎'-assoc' {F = `Σ _ T} (s , t) = s , ◎'-assoc' {F = T s} t
◎'-assoc' {F = `Π _ T} f s = ◎'-assoc' {F = T s} (f s)
◎'-assoc' {F = F₁ `× F₂} (x , y) = ◎'-assoc' {F = F₁} x , ◎'-assoc' {F = F₂} y
◎'-assoc' {F = `σ _ T} (n , t) = n , ◎'-assoc' {F = T n} t

◎-assoc' : ∀ {I J K}{F G H}{X : I → Set} → ⟦_⟧func {J = K} ( F ◎ (G ◎ H) ) X ⇒ ⟦ _◎_ {J = J} (_◎_ {J = J} F G) H ⟧func X
◎-assoc' {F = mk F}{i = i} = ◎'-assoc' {F = F i}

◎'-assoc'' : ∀ {I J}{F G H}{X : I → Set} → ⟦ _◎'_ {J = J} (_◎'_ {J = J} F G) H ⟧ X → ⟦ F ◎' func.out (mk G ◎ mk H) ⟧ X
◎'-assoc'' {F = `var _} = id
◎'-assoc'' {F = `1} = id
◎'-assoc'' {F = `Σ _ T} (s , t) = s , ◎'-assoc'' {F = T s} t
◎'-assoc'' {F = `Π _ T} f s = ◎'-assoc'' {F = T s} (f s)
◎'-assoc'' {F = F₁ `× F₂} (x , y) = ◎'-assoc'' {F = F₁} x , ◎'-assoc'' {F = F₂} y
◎'-assoc'' {F = `σ _ T} (n , t) = n , ◎'-assoc'' {F = T n} t

◎-assoc'' : ∀ {I J K}{F G H}{X : I → Set} → ⟦ _◎_ {J = J} (_◎_ {J = J} F G) H ⟧func X ⇒ ⟦_⟧func {J = K} ( F ◎ (G ◎ H) ) X
◎-assoc'' {F = mk F}{i = i} = ◎'-assoc'' {F = F i}

◎'-⟦⟧-distrib' : ∀ {I J}{F G}{X : I → Set} → ⟦_⟧ {I = J} F (⟦ G ⟧func X) → ⟦ F ◎' func.out G ⟧ X
◎'-⟦⟧-distrib' {F = `var i} = id
◎'-⟦⟧-distrib' {F = `1} = id
◎'-⟦⟧-distrib' {F = `Σ _ T} (s , t) = s , ◎'-⟦⟧-distrib' {F = T s} t
◎'-⟦⟧-distrib' {F = `Π _ T} f s = ◎'-⟦⟧-distrib' {F = T s} (f s)
◎'-⟦⟧-distrib' {F = F₁ `× F₂} (x , y) = ◎'-⟦⟧-distrib' {F = F₁} x , ◎'-⟦⟧-distrib' {F = F₂} y
◎'-⟦⟧-distrib' {F = `σ _ T} (n , t) = n , ◎'-⟦⟧-distrib' {F = T n} t

◎-⟦⟧-distrib' : ∀ {I J K}{F G}{X : I → Set} → ⟦_⟧func {I = J} {J = K} F (⟦ G ⟧func X) ⇒ ⟦ F ◎ G ⟧func X
◎-⟦⟧-distrib' {F = mk F} {i = i} = ◎'-⟦⟧-distrib' {F = F i}

◎'-⟦⟧-distrib'' : ∀ {I J}{F G}{X : I → Set} → ⟦ F ◎' func.out G ⟧ X → ⟦_⟧ {I = J} F (⟦ G ⟧func X) 
◎'-⟦⟧-distrib'' {F = `var i} = id
◎'-⟦⟧-distrib'' {F = `1} = id
◎'-⟦⟧-distrib'' {F = `Σ _ T} (s , t) = s , ◎'-⟦⟧-distrib'' {F = T s} t
◎'-⟦⟧-distrib'' {F = `Π _ T} f s = ◎'-⟦⟧-distrib'' {F = T s} (f s)
◎'-⟦⟧-distrib'' {F = F₁ `× F₂} (x , y) = ◎'-⟦⟧-distrib'' {F = F₁} x , ◎'-⟦⟧-distrib'' {F = F₂} y
◎'-⟦⟧-distrib'' {F = `σ _ T} (n , t) = n , ◎'-⟦⟧-distrib'' {F = T n} t

◎-⟦⟧-distrib'' : ∀ {I J K}{F G}{X : I → Set} → ⟦ F ◎ G ⟧func X ⇒ ⟦_⟧func {I = J} {J = K} F (⟦ G ⟧func X)
◎-⟦⟧-distrib'' {F = mk F} {i = i} = ◎'-⟦⟧-distrib'' {F = F i}
