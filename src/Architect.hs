-- Find possible values for a given type in System F

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Seeker
  where

import           GHC.Types (Type)

import           Control.Monad

import           Data.Functor.Classes
import           Data.Foldable

import           Text.Show.Deriving

import           Bound

-- data Nat = Z | S Nat

data Ty n
  = BaseTy String
  | TyVar n
  | Ty n :-> Ty n
  | AppTy (Ty n) (Ty n)
  -- | ForallTy (Name n) (Ty n)
  | ForallTy (Scope () Ty n)
  | PairTy (Ty n) (Ty n)
  | EitherTy (Ty n) (Ty n)
  | VoidTy
  | UnitTy
  deriving (Functor, Foldable, Traversable)

deriveShow1 ''Ty

deriving instance Show n => Show (Ty n)

instance Applicative Ty where
  pure = return
  (<*>) = ap

instance Monad Ty where
  return = TyVar
  TyVar n >>= f = f n
  BaseTy str >>= _ = BaseTy str
  (x :-> y) >>= f = (x >>= f) :-> (y >>= f)
  AppTy x y >>= f = AppTy (x >>= f) (y >>= f)
  ForallTy s >>= f = ForallTy (s >>>= f)
  PairTy x y >>= f = PairTy (x >>= f) (y >>= f)
  EitherTy x y >>= f = EitherTy (x >>= f) (y >>= f)
  VoidTy >>= _ = VoidTy
  UnitTy >>= _ = UnitTy

data Expr :: Type -> Type where
  Unit :: Expr n
  Var :: n -> Expr n

  Lam :: Scope () Expr n -> Expr n

  App :: Expr n -> Expr n -> Expr n
  Pair :: Expr n -> Expr n -> Expr n
  InL :: Expr n -> Expr n
  InR :: Expr n -> Expr n

  -- Ann :: Expr n -> Ty m -> Expr n

deriveShow1 ''Expr

deriving instance Functor Expr
deriving instance Foldable Expr
deriving instance Traversable Expr
deriving instance Show n => Show (Expr n)

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  Var n >>= f = f n

  Lam s >>= f = Lam (s >>>= f)
  App x y >>= f = App (x >>= f) (y >>= f)
  Pair x y >>= f = Pair (x >>= f) (y >>= f)
  InL x >>= f = InL (x >>= f)
  InR y >>= f = InR (y >>= f)

  -- Ann e ty >>= f = Ann (e >>= f) ty

