module 00-All-Utilities where

open import Data.Nat using (ℕ; zero; suc)
import Data.List as L
open import Data.List.Relation.Unary.All  

top : ∀ {A : Set}{xs ys : L.List A}{P : A → Set} → All P (xs L.++ ys) → All P xs
top {A} {L.[]} {ys} {P} pxs = []
top {A} {x L.∷ xs} {ys} {P} (px ∷ pxs) = px ∷ top pxs

bot : ∀ {A : Set}{xs ys : L.List A}{P : A → Set} → All P (xs L.++ ys) → All P ys
bot {A} {L.[]} {ys} {P} pxs = pxs
bot {A} {x L.∷ xs} {ys} {P} (px ∷ pxs) = bot pxs

take : ∀ {A : Set}{xs : L.List A}{P : A → Set} n → All P xs → All P (L.take n xs)
take zero pxs = []
take (suc n) [] = []
take (suc n) (px ∷ pxs) = px ∷ take n pxs

drop : ∀ {A : Set}{xs : L.List A}{P : A → Set} n → All P xs → All P (L.drop n xs)
drop zero pxs = pxs
drop (suc n) [] = []
drop (suc n) (px ∷ pxs) = drop n pxs

infixr 10 _++_
_++_ : ∀ {A : Set}{xs ys : L.List A}{P : A → Set} → All P xs → All P ys → All P (xs L.++ ys)
[] ++ pys = pys
(px ∷ pxs) ++ pys = px ∷ (pxs ++ pys)
