{-# OPTIONS --prop #-}
{-# OPTIONS --guardedness #-}

module predicatesEG where

open import Level using (Level; 0ℓ; _⊔_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Polymorphic.Base
open import Function.Base using (_∘′_; _$′_; const; flip)

open import Data.Empty
open import Data.Unit 
open import Data.Product
open import Data.List
open import Data.Maybe

open import Data.List.Relation.Unary.Any

open import Data.Nat hiding ( _⊔_ )

open import Data.Bool


private 
  variable
    ℓ ℓ' ℓ'' : Level

---------------------------
-- PRELIMINARIES
---------------------------

record Stream (A : Set  ℓ) : Set ℓ where
  coinductive
  constructor cons'
  field
    hd : A
    tl : Stream A

data _≡_ {A : Set  ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

infix 4 _≡P_
data _≡P_ {a} {A : Set a} (x : A) : A → Prop a where
  instance refl : x ≡P x

record ⊤P : Prop where
  constructor ttP

data ⊥P : Prop where

infix 3 ¬Prop
¬Prop : Prop ℓ → Prop ℓ
¬Prop P = P → ⊥P

Levels : ℕ → Set
Levels zero    = Data.Unit.Polymorphic.Base.⊤
Levels (suc n) = Level × Levels n

⨆ : ∀ n → Levels n → Level
⨆ zero    _        = Level.zero
⨆ (suc n) (l , ls) = l ⊔ (⨆ n ls)

-- take a 'type' U - a 'predicate' on it is defined as:
Predicate : {ℓ ℓ' : Level} → (U : Set ℓ) → (Set (ℓ ⊔ Level.suc ℓ'))
Predicate {ℓ}{ℓ'} U = (U → Prop ℓ')

-- NEGATION WITH PREDICATES --  (binary 'And' and 'Or' are no more difficult)
NotP : {ℓ ℓ' : Level} → {U : Set ℓ} → Predicate {ℓ}{ℓ'} U → Predicate {ℓ}{ℓ'} U
NotP {ℓ}{ℓ'}{U} pu = λ x → ¬Prop (pu x)

-- example:
is0-ℕ : ℕ → Prop (Level.zero)
is0-ℕ n = n ≡P 0   

is0-ℕ-of-0 : is0-ℕ 0
is0-ℕ-of-0 = refl

¬is0-ℕ-of-1 : is0-ℕ 1 → ⊥
¬is0-ℕ-of-1 ()

allℕ : ℕ → Prop (Level.zero)
allℕ n = ⊤P

-- And it is a 'predicate' on ℕ:
is0-ℕ-isPredicate : Predicate {_}{Level.zero} ℕ  
is0-ℕ-isPredicate n = is0-ℕ n

-- simple possible example of a union of a List of predicates:
data ListUnionℕ-level0 : List (Predicate {_}{Level.zero} ℕ) → (Predicate {_} {Level.suc Level.zero}  ℕ)  where
  all-n-such-that : {x : ℕ} → (myList : List (Predicate {_}{Level.zero} ℕ)) → (pred : Predicate {_} {Level.zero} ℕ) → (membership : Any (_≡_ pred) myList) → (instance-pred : pred x) → (ListUnionℕ-level0 myList) x 

-- Example of a union of a List of predicates, with Any universe type U as a parameter, level of predicate = 0:
data ListUnionU-level0 (U : Set ℓ) : List (Predicate {ℓ}{Level.zero} U) → (Predicate {ℓ} {(ℓ ⊔ Level.suc Level.zero)}  U)  where
  all-x-such-that : {x : U} → (myList : List (Predicate {ℓ}{Level.zero} U)) → (pred : Predicate {ℓ} {Level.zero} U) → (membership : Any (_≡_ pred) myList) → (instance-pred : pred x) → (ListUnionU-level0 U myList) x


-- Example of a union of a List of predicates, with Any universe type U as a parameter, level of predicate is parameter ℓ':
data ListUnionU-levelℓ' (ℓ' : Level) (U : Set ℓ) : List (Predicate {ℓ}{ℓ'} U) → (Predicate {ℓ} {(ℓ ⊔ Level.suc ℓ')}  U) where
  all-x-such-that : {x : U} → (myList : List (Predicate {ℓ}{ℓ'} U)) → (pred : Predicate {ℓ} {ℓ'} U) → (membership : Any (_≡_ pred) myList) → (instance-pred : pred x) → (ListUnionU-levelℓ' ℓ' U myList) x

Pred : ∀ {ℓ'} → Set ℓ' → (ℓ : Level) → Set (ℓ'  ⊔ Level.suc ℓ)
Pred A ℓ = A → Set ℓ

data Any' {A : Set ℓ} (P : Pred A ℓ') : Pred (Stream A) (ℓ ⊔  ℓ') where
  here'  : ∀ {x xs} (px  : P x)      → Any' P (cons' x xs)
  there' : ∀ {x xs} (pxs : Any' P xs) → Any' P (cons' x xs)

-- Example of an INFINITE union of a Stream of predicates (could equally be a CoList), with Any universe type U as a parameter, level of predicate is parameter ℓ':
data StreamUnionU-levelℓ' (ℓ' : Level) (U : Set ℓ) : Stream (Predicate {ℓ}{ℓ'} U) → (Predicate {ℓ} {(ℓ ⊔ Level.suc ℓ')}  U) where
  all-x-such-that : {x : U} → (myStream : Stream (Predicate {ℓ}{ℓ'} U)) → (pred : Predicate {ℓ} {ℓ'} U) → (membership : Any' (_≡_ pred) myStream) → (instance-pred : pred x) → (StreamUnionU-levelℓ' ℓ' U myStream) x


