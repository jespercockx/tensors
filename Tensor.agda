
open import Level using (Level)
open import Function using (case_of_; case_return_of_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _+_)
open import Data.List as List using (List; []; _∷_; _++_; reverse; reverseAcc)
open import Data.Vec as Vec using (Vec; []; _∷_; replicate)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable
  ℓ : Level
  A B C : Set ℓ
  x y z : A
  xs ys zs : List A
  m n : ℕ

infix 3 _⊆_

it : {{A}} → A
it {{x}} = x

data _⊆_ {A : Set ℓ} : List A → List A → Set where
  end  :               [] ⊆ []
  keep : xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  drop : xs ⊆ ys →     xs ⊆ x ∷ ys

[]⊆xs : [] ⊆ xs
[]⊆xs {xs = []} = end
[]⊆xs {xs = x ∷ xs} = drop []⊆xs

try-⊆ : (xs ys : List ℕ) → List (xs ⊆ ys)
try-⊆ [] ys = []⊆xs ∷ []
try-⊆ (x ∷ xs) [] = []
try-⊆ (x ∷ xs) (y ∷ ys) = case x ≟ y of λ where
  (yes refl) → List.map keep (try-⊆ xs ys) ++ List.map drop (try-⊆ (x ∷ xs) ys)
  (no ¬p   ) → List.map drop (try-⊆ (x ∷ xs) ys)

data ShouldBeSingleton : List A → Set where

IsSingleton : List A → Set
IsSingleton (x ∷ []) = ⊤
IsSingleton xs       = ShouldBeSingleton xs

instance
  ⊆-unique : {{IsSingleton (try-⊆ xs ys)}} → xs ⊆ ys
  ⊆-unique {xs = xs} {ys = ys} with try-⊆ xs ys
  ⊆-unique | p ∷ [] = p

⊆-test₁ : [] ⊆ (3 ∷ 5 ∷ [])
⊆-test₁ = it

⊆-test₂ : 3 ∷ [] ⊆ 1 ∷ 3 ∷ 5 ∷ []
⊆-test₂ = it

⊆-test₃ : 3 ∷ [] ⊆ 3 ∷ 3 ∷ []
⊆-test₃ = {!it!}

record Scalar (A : Set ℓ) : Set ℓ where
  constructor [_]
  field unScalar : A
open Scalar

Tensor : Set ℓ → List ℕ → Set ℓ
Tensor A []       = Scalar A
Tensor A (n ∷ ns) = Vec (Tensor A ns) n

Tensor-test₁ : Tensor A _ ≡ Vec (Vec (Scalar A) 3) 5
Tensor-test₁ = refl

lift : {{xs ⊆ ys}} → Tensor A xs → Tensor A ys
lift ⦃ end    ⦄ x   = x
lift ⦃ keep p ⦄ xss = Vec.map (lift ⦃ p ⦄) xss
lift ⦃ drop p ⦄ xss = replicate (lift ⦃ p ⦄ xss)

lift-test₁ : A → Vec (Vec (Scalar A) 3) 5
lift-test₁ x = lift [ x ]

lift-test₂ : Tensor A (3 ∷ []) → Tensor A (1 ∷ 3 ∷ 5 ∷ [])
lift-test₂ x = lift x

_+Tensor′_ : Tensor ℕ xs → Tensor ℕ xs → Tensor ℕ xs
_+Tensor′_ {xs = []} [ a ] [ b ] =  [ a + b ]
_+Tensor′_ {xs = x ∷ xs} as bs = Vec.zipWith _+Tensor′_ as bs

_+Tensor_ : {{_ : xs ⊆ zs}} {{_ : ys ⊆ zs}} → Tensor ℕ xs → Tensor ℕ ys → Tensor ℕ zs
_+Tensor_ {{xszs}} {{yszs}} xss yss = lift {{xszs}} xss +Tensor′ lift {{yszs}} yss

+Tensor-test₁ : Tensor ℕ (5 ∷ 2 ∷ 3 ∷ 2 ∷ [])
+Tensor-test₁ = xss +Tensor yss
  where
    xss : Tensor ℕ (2 ∷ 2 ∷ [])
    xss = ([ 2 ] ∷ [ 5 ] ∷ []) ∷ ([ 3 ] ∷ [ 9 ] ∷ []) ∷ []

    yss : Tensor ℕ (3 ∷ [])
    yss = [ 0 ] ∷ [ 10 ] ∷ [ 100 ] ∷ []


mapTensor : (f : A → B) → Tensor A xs → Tensor B xs
mapTensor {xs = []} f [ x ] = [ f x ]
mapTensor {xs = x ∷ xs} f xss = Vec.map (mapTensor f) xss

transposeAcc : Tensor (Tensor A xs) ys → Tensor A (reverseAcc ys xs)
transposeAcc {xs = []}    xss = mapTensor unScalar xss
transposeAcc {xs = _ ∷ _} xss =
  transposeAcc (Vec.tabulate λ i →
    mapTensor (λ xs → Vec.lookup xs i) xss)

transpose : Tensor A xs → Tensor A (reverse xs)
transpose xss = transposeAcc [ xss ]

testTranspose₁ : Tensor ℕ (2 ∷ 2 ∷ [])
testTranspose₁ = transpose mat
  where
    mat : Tensor ℕ (2 ∷ 2 ∷ [])
    mat = (([ 1 ] ∷ [ 2 ] ∷ [])
         ∷ ([ 3 ] ∷ [ 4 ] ∷ []) ∷ [])
