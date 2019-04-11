module Exam where

-- Base declarations --
infix 4 _==_
data _==_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x == x
{-# BUILTIN EQUALITY _==_  #-}

record Unit : Set where
{-# BUILTIN UNIT Unit #-}

data List (a : Set) : Set where
  [] : List a
  _::_ : a -> List a -> List a

-- Exercise setup --

-- types, either base type i, or a function type for types σ and τ.
data U : Set where
  i    : U
  _=>_ : U -> U -> U

-- a context, is a list of types.
Ctx = List U

-- we represent a variable of type s, by providing a 'proof' that s occurs in
-- the context Γ, given by data type s ∈ Γ.
data _∈_ (s : U) : Ctx -> Set where
  Top : ∀ { ctx }   -> s ∈ (s :: ctx)
  Pop : ∀ { ctx t } -> s ∈ ctx -> s ∈ (t :: ctx)

-- well-typed lambda terms, Term, with variables drawn from the context Γ.
data Term (Γ : Ctx) : U -> Set where
  var : ∀ {   τ } -> τ ∈ Γ             -> Term Γ τ
  app : ∀ { σ τ } -> Term Γ ( σ => τ ) -> Term Γ σ -> Term Γ τ
  lam : ∀ { σ τ } -> Term ( σ :: Γ ) τ -> Term Γ (σ => τ)

-- the careful choice of type indices, enables us to define a simple evaluator
-- that caries around an environment that contains values,
-- for all the free variables in the term.
Val : U -> Set
Val i        = Unit
Val (σ => τ) = Val σ -> Val τ

data Env : Ctx -> Set where
  Nil  : Env [] -- Env Nil?
  Cons : ∀ { u ctx } -> Val u -> Env ctx -> Env (u :: ctx)

-- Exercise a; Define the missing lookup
lookup : ∀ { s Γ } -> s ∈ Γ -> Env Γ -> Val s
lookup Top (Cons x y)      = x
lookup (Pop x) (Cons y ys) = lookup x ys

eval : ∀ { Γ σ } -> Term Γ σ -> Env Γ -> Val σ
eval (app t1 t2) env = (eval t1 env) (eval t2 env)
eval (lam body) env  = λ x -> eval body (Cons x env)
eval (var j) env     = lookup j env

-- Exercise b; Define a data tpe for well-typed combinator terms:
--   - the atomic combinators S, K and I
--   - the application of one combinator to another
--   - variables drawn from some context
-- ! this term language should not include a constructor for lamdas.
-- ! choose your datatupe so that it can only represent well-typed SKI terms
-- HINT: You may want to use ghci to check the types of the three atomic combinators for you

-- Exercise c; Define an interpretation function evalSKI
-- given an SKI term of type σ, and an env, produce value of type Val σ

-- Exercise d; Define a translation from lambda terms, Term Γ σ to your SKI datatype
-- hint: define an auxiliary function lamda to handle the case for abstractions lam (what is its type?)

-- Exercise e; formulate the property that the translation is correct, prove this for applications and variables
-- What goes wrong when you try to prove the branch for lamda abstractions?
-- What property can you formulate and prove that relates evalSKI and the auxiliary lambda function?

