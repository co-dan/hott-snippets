{-# OPTIONS --without-K #-}
{--
http://www.cs.bham.ac.uk/~mhe/yoneda/yoneda.html
--}

U = Set
U₁ = Set₁

data Hom {X : U} : X -> X -> U where
  idp : (x : X) -> Hom x x

inv : {X : U} -> {x y : X} -> Hom x y -> Hom y x
inv (idp x) = idp x

PrShf : U -> U₁
PrShf X = (X -> U)

y : {X : U} -> X -> PrShf X 
y a b = Hom b a

Nat : {X : U} -> (X -> U) -> (X -> U) -> U
Nat {X} F G = (x : X) → F x → G x

yoneda-elem : {C : U} -> {X : C} {F : PrShf C} -> Nat (y X) F -> F X
yoneda-elem {C} {X} η = η X (idp X)

yoneda-nat : {C : U} -> {X : C} {F : PrShf C} -> F X -> Nat (y X) F
yoneda-nat x X (idp .X) = x

transport : {A : U} -> (P : A -> U) -> {x y : A} -> Hom x y -> P x -> P y
transport P {x} {y} p a = yoneda-nat {F = P} a y (inv p)
