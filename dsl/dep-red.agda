{-# OPTIONS --guardedness #-}

module dep-red where

open import Relation.Binary.PropositionalEquality
open import Algebra.Definitions
open import Data.Product
open import Data.Nat
open import Data.Nat.Show
open import Data.Nat.Properties
open import Data.String
open import Data.Unit
open import Data.Sum
open import Data.Vec

open import IO
-- Helpers --------------------------------------------------------------------------

natShow = Data.Nat.Show.show
_+s+_ = Data.String._++_
_+v+_ = Data.Vec._++_

vecLookup = Data.Vec.lookup

-- The following is modified from the 2.0 agda library, which has yet to be packaged for ubuntu
-- Note we're defining division by 0, which is undefined, but this simplifies our typesystem for the purposes of this demo.

div-helper : (k m n j : ℕ) → ℕ
div-helper k m  zero    j      = k
div-helper k m (suc n)  zero   = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k       m n j

_/_ : (dividend divisor : ℕ) → ℕ
m / 0 = 0
m / (suc n) = div-helper 0 n m n

mod-helper : (k m n j : ℕ) → ℕ
mod-helper k m  zero    j      = k
mod-helper k m (suc n)  zero   = mod-helper 0       m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

_%_ : (dividend divisor : ℕ) → ℕ
m % 0 = 0
m % (suc n) = mod-helper 0 n m n


-- term definition  ----------------------------------------------------

-- here lies an ill-fated attempt at an inductive definition, it will be missed

--               ____
--            __|2 0|__
--           |__ 2 3 __|
--              | R |
--              | I |
--        ______|_P_|_______________
-- ~~~~~/___________________________\~~~~~~~~~~~~~~~~~~~~~

-- data Term (X : Set) : (order : ℕ) → (Vec Set order) → Set where
--     closedTerm : X → String → Term X 0 []
--     openTerm   : ∀ {o b} → (Y : Set) → (Binding Y → (Term X o b)) → (Term X (suc o) (Y ∷ b))

-- ind-Term : {X : Set} → (order : ℕ) → (bindings : Vec Set order) →
--            (Term X order bindings) →
--            (motive : ∀ o b → Set) →
--            (motive 0 []) →
--            (∀ o₂ b₂ Y → (Binding Y → (Term X o₂ b₂)) → (motive o₂ b₂) → (motive (suc o₂) (Y ∷ b₂))) →
--            (motive order bindings)
-- ind-Term 0 [] _ _ base _ = base
-- ind-Term (suc n) (Y ∷ b) (openTerm Y subTerm) mot base step =
--     (step n b Y subTerm (ind-Term n b () base step))  -- this doesn't work!!!!

-- bind : ∀ {X Y o b} → String → (Term X (suc o) (Y ∷ b)) → (Term (Y → X) o b)
-- bind bindingName (openTerm Y subTerm) = ?

fnOfType : ∀ {order} → (Vec Set order) → Set → Set 
fnOfType (Y ∷ b) X = fnOfType b (Y → X) -- carefully chosen to allow for syntactic reduction
fnOfType [] X = X

fnOfStr : ℕ → Set
fnOfStr 0 = String
fnOfStr (suc n) = String → (fnOfStr n)

data Term (X : Set) : (order : ℕ) → (Vec Set order) → Set where
    term : ∀ o → (b : Vec Set o) → (fnOfType b X) → (fnOfStr o) → (Term X o b)

-- variable introduction --

-- More work needs to be done in order to support binding with arbitrary depth;
-- The below is a skeleton, but the rest of the DSL will be written assuming exactly two bindings.
-- Turns out dependent types are complicated!

-- ignoreWith : ∀ {X} o → (t : Vec Set o) → X → (fnOfType t X)
-- ignoreWith 0 [] x = x
-- ignoreWith (suc n) (_ ∷ t) x = ignoreWith n t (λ y → x)

-- ignoreStrWith : ∀ o → (String → String) → (fnOfStr (suc o))
-- ignoreStrWith 0 base = base
-- ignoreStrWith (suc n) x = λ y → ignoreStrWith n x

-- given a binding context, make an open term recovering Y
-- var : (oₕ oₜ : ℕ) → (h : Vec Set oₕ) → (Y : Set) → (t : Vec Set oₜ) → Term Y (oₕ + (suc oₜ)) (h +v+ (Y ∷ t))
-- var 0 0 [] Y [] = term 1 (Y ∷ []) (λ x → x) (λ x → x)
-- var 0 (suc o) [] Y (Z ∷ t) with var 0 o [] Y t
-- ...                   | (term _ _ genTerm genStr) = ?   -- We need to induct on fnOfType to prove base can be pulled to head
-- var (suc o) oₜ (X ∷ h) Y t with var o oₜ h Y t
-- ...                   | (term _ _ genTerm genStr) = ?


-- our simplified binding terms:

var0 : (X Y : Set) → Term X 2 (X ∷ Y ∷ [])
var0 X Y = term 2 (X ∷ Y ∷ []) (λ y x → x) (λ y x → x)

var1 : (X Y : Set) → Term Y 2 (X ∷ Y ∷ [])
var1 X Y = term 2 (X ∷ Y ∷ []) (λ y x → y) (λ y x → y)

-- -- A Small DSL ----------------------------------------------------------------------

-- helpers --

eOp : (ℕ → ℕ → ℕ) → (String → String → String) → (Term ℕ 2 (ℕ ∷ ℕ ∷ [])) → (Term ℕ 2 (ℕ ∷ ℕ ∷ [])) → (Term ℕ 2 (ℕ ∷ ℕ ∷ []))
eOp fn stx (term _ _ genTermA genStrA) (term _ _ genTermB genStrB) =
    term 2 (ℕ ∷ ℕ ∷ []) (λ x y → fn (genTermA x y) (genTermB x y)) (λ x y → stx (genStrA x y) (genStrB x y))

recoverTerm : ∀ {X} → (Term X 0 []) → X
recoverTerm (term 0 [] t s) = t

recoverStr : ∀ {X} → (Term X 0 []) → String
recoverStr (term 0 [] t s) = s

wrapStr : ∀ (n : ℕ) → (fnOfStr n) → (String → String) → (fnOfStr n)
wrapStr 0 base f = f base
wrapStr (suc n) base f = λ s → wrapStr n (base s) f

-- user bindings --

-- push named applications down into our type
eBind : ∀ {X Y o b} → String → (Term X (suc o) (Y ∷ b)) → (Term (Y → X) o b)
eBind name (term (suc o) (Y ∷ b) genTerm genStr) =
    term o b genTerm
    (wrapStr o (genStr name) (λ term → "fun (" +s+ (name +s+ (") -> " +s+ (term +s+ " end")))))

eVar0N = var0 ℕ ℕ
eVar1N = var1 ℕ ℕ

eNum : ℕ → (Term ℕ 2 (ℕ ∷ ℕ ∷ []))
eNum n = term 2 (ℕ ∷ ℕ ∷ []) (λ x y → n) (λ x y → natShow n)

_e+_ = eOp (λ a b → a + b) (λ a b → a +s+ (" + " +s+ b))
_e*_ = eOp (λ a b → a * b) (λ a b → a +s+ (" * " +s+ b))

_e/_ = eOp (λ a b → a / b) (λ a b → a +s+ (" div " +s+ b))
_e%_ = eOp (λ a b → a % b) (λ a b → a +s+ (" rem " +s+ b))

_e⊓_ = eOp (λ a b → a ⊓ b) (λ a b → "min(" +s+ (a +s+ (", " +s+ (b +s+ ")"))))
_e⊔_ = eOp (λ a b → a ⊔ b) (λ a b → "max(" +s+ (a +s+ (", " +s+ (b +s+ ")"))))

-- rerverses binding order compared to stdlib
associative : (X : Set) → (f : (X → X → X)) → Set
associative X f = (c b a : X) → (f a (f b c)) ≡ (f (f a b) c)

-- Our well-typed call to reduce, which requires a proof of associativity
eReduce : {X : Set} → (t : Term (X → X → X) 0 []) → (associative X (recoverTerm t)) → (Term ⊤ 0 [])
eReduce (term 0 [] t str) _ =
    term 0 [] tt
    ("-module(test).
-export([start/0]).

start() -> reduce:reduce_test(100, fun (A, B) -> apply(apply(" +s+ (str +s+ ", [A]), [B]) end)."))

-- Now for some examples!

redFun1 = eBind "X" (eBind "Y" (eVar0N e+ eVar1N)) -- associative and commutative
redFun2 = eBind "X" (eBind "Y" (eVar0N e⊔ eVar1N)) -- associative and commutative
redFun3 = eBind "X" (eBind "Y" ((eVar0N e* (eNum 2)) e⊔ (eVar1N e+ (eNum 1)))) -- neither associative nor commutative, cannot be typed for a reduce
redFun4 = eBind "X" (eBind "Y" (eVar0N e+ (eVar1N e* (eNum 0)))) -- associative but not commutative

-- prove associativity for redFun4
assoc4 : (a b c : ℕ) → ((a + (b * 0)) + (c * 0)) ≡ (a + ((b + (c * 0)) * 0)) 
assoc4 a b c rewrite *-zeroʳ (b + (c * 0))
   rewrite *-zeroʳ b
   rewrite *-zeroʳ c
   rewrite +-identityʳ a = +-identityʳ a

reduction1 = eReduce redFun1 +-assoc
reduction2 = eReduce redFun2 ⊔-assoc

-- Type a more complicated example for reduce, with associativity proof satisfying our constraint
reduction4 = eReduce redFun4 assoc4

-- Spit out some Erlang:

main : Main
main = run (writeFile "test.erl" (recoverStr reduction4))

