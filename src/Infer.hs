{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Wno-unused-imports #-}

module Infer
  where

import           Seeker

import           Bound
import           Bound.Var
import           Bound.Scope

import           Control.Applicative
import           Control.Monad.State

import           Control.Arrow ((***), (&&&))

import           Data.Bifunctor

import           Data.Foldable

data Name = Name { nameStr :: String, nameUniq :: Int }
  deriving (Eq, Ord)

-- instance Eq Name where
--   Name _ x == Name _ y = x == y

-- instance Ord Name where
--   compare (Name _ x) (Name _ y) = compare x y

newtype Ctx a b = Ctx [(a, Ty b)]

instance Bifunctor Ctx where
  bimap f g (Ctx c) = Ctx $ map (f *** fmap g) c

instance Functor (Ctx a) where
  fmap = second

ctxLookup :: Eq a => a -> Ctx a b -> Maybe (Ty b)
ctxLookup x (Ctx c) = lookup x c

ctxExtend :: a -> Ty b -> Ctx a b -> Ctx a b
ctxExtend x ty (Ctx c) = Ctx ((x, ty) : c)

ctxExtendBound :: Ty b -> Ctx a b -> Ctx (Var () a) b
ctxExtendBound ty = ctxExtend (B ()) ty . first F

-- | Constraint
data Ct a = Ct (Ty a) (Ty a)

data InferState n =
  InferState
    { ctUniq :: Int
    , exprUniq :: Int
    , inferStateCts :: [Ct n]
    }

type InferError = () -- TODO: Descriptive errors

newtype Infer n a = Infer (StateT (InferState n) (Either InferError) a)
  deriving (Functor, Applicative, Monad, MonadState (InferState n))

class Fresh n where
  fresh :: Infer n n

-- named :: Traversable t => t String -> t Name
-- named = flip evalState 0 . mapM go
--   where
--     go str = do
--       currUniq <- get
--       modify succ
--       pure (Name str currUniq)

runInfer :: Infer n a -> Either InferError a
runInfer (Infer i) = evalStateT i InferState { ctUniq = 0, exprUniq = 0, inferStateCts = [] }

inferError :: InferError -> Infer n a
inferError x = Infer $ lift $ Left x

newCtName :: Infer n Name
newCtName = do
  currUniq <- ctUniq <$> get

  modify (\is -> is { ctUniq = succ (ctUniq is) })

  return (Name "alpha" currUniq)

newExprName :: Infer n Name
newExprName = do
  currUniq <- exprUniq <$> get

  modify (\is -> is { exprUniq = succ (exprUniq is) })

  return (Name "x" currUniq)


pushCt :: Ct a -> Infer a ()
pushCt ct = modify (\is -> is { inferStateCts = ct : inferStateCts is })

-- (.=) :: Ty Name -> Ty Name -> Infer Name
-- a .= b = do
--   name <- 

-- freshTyVar :: Ty Name -> Infer n Name
-- freshTyVar ty = do
--   name <- newCtName
--   pushCt (Ct (TyVar name) ty)
--   pure name


solve :: Infer n a -> Maybe a
solve = undefined

-- ensureUniqInvariant_Ty :: [Ty Name] -> Infer ()
-- ensureUniqInvariant_Ty tys =
--   case concatMap toList tys of
--     [] -> pure ()
--     (x:xs) -> do
--       let theMax = maximum (x:xs)
--       currUniq <- ctUniq <$> get

--       if currUniq <= nameUniq theMax
--         then do
--           modify (\is -> is { ctUniq = succ (nameUniq theMax) })
--         else
--           pure ()

-- ensureUniqInvariant_Expr :: Expr Name -> Infer ()
-- ensureUniqInvariant_Expr expr =
--   case toList expr of
--     [] -> pure ()
--     (x:xs) -> do
--       let theMax = maximum (x:xs)
--       currUniq <- exprUniq <$> get

--       if currUniq <= nameUniq theMax
--         then do
--           modify (\is -> is { exprUniq = succ (nameUniq theMax) })
--         else
--           pure ()

unify :: Ty a -> Ty a -> Infer a (Ty a)
unify = undefined
-- unify ty1 ty2 =
--   go ty1 ty2
--   where
--     go :: Ty a' -> Ty a' -> Infer a' (Ty a')
--     go (BaseTy a) (BaseTy b)
--       | a == b = pure $ (BaseTy a)
--       | otherwise = inferError ()

--     go tyA@(TyVar a) tyB@(TyVar b)
--       | a == b = pure tyA
--       | otherwise = do
--           pushCt (Ct tyA tyB)
--           pure tyA

--     go (a :-> b) (a' :-> b') =
--       liftA2 (:->) (go a a') (go b b')

--     go (AppTy f x) (AppTy f' x') =
--       AppTy <$> go f f' <*> go x x'

--     go (ForallTy s) (ForallTy s') = do
--       -- freshName <- newCtName

--       -- -- let freshVar = TyVar freshName
--       -- let s_inst  = instantiate1 (TyVar freshName) s
--       --     s'_inst = instantiate1 (TyVar freshName) s'

--       let s_inst = fromScope s
--           s'_inst = fromScope s'

--       first (unvar _ id) $ (const (ForallTy s)) <$> (go s_inst s'_inst)

--     go (PairTy x y) (PairTy x' y') =
--       PairTy <$> go x x' <*> go y y'

--     go VoidTy VoidTy = pure VoidTy
--     go UnitTy UnitTy = pure UnitTy
--     go _ _ = inferError ()

check :: forall a b. Eq a => Ctx a b -> Expr a -> Ty b -> Infer b (Ty b)
check ctx0 expr0 ty0 =
  go ctx0 expr0 ty0
  where
    go :: Eq a' => Ctx a' b' -> Expr a' -> Ty b' -> Infer b' (Ty b')
    go _ Unit UnitTy = pure UnitTy

    go ctx (InL x) (EitherTy a b) =
      EitherTy <$> go ctx x a <*> pure b

    go ctx (InR y) (EitherTy a b) =
      EitherTy <$> pure a <*> go ctx y b

    go ctx (Pair x y) (PairTy a b) =
      PairTy <$> go ctx x a <*> go ctx y b

    go ctx (App f x) resTy = do
      argTy <- infer ctx x
      go ctx f (argTy :-> resTy)

    go ctx (Lam f) (a :-> b) = do
      let body = fromScope f

      resTy <- go (ctxExtendBound a ctx) body b

      pure (a :-> resTy)

    go ctx (Var x) ty =
      case ctxLookup x ctx of
        Nothing  -> pure ty
        Just ty' -> unify ty ty'

    go _ _ _ = inferError ()

infer :: Ctx a b -> Expr a -> Infer b (Ty b)
infer = undefined
-- infer ctx0 expr0 = do
--   ensureUniqInvariant_Expr expr0
--   go ctx0 expr0
--   where
--     go _ Unit = pure UnitTy
--     go ctx (InL x) =
--       EitherTy <$> go ctx x <*> fmap TyVar newCtName
--     go ctx (InR y) =
--       EitherTy <$> fmap TyVar newCtName <*> go ctx y
--     go ctx (Pair x y) =
--       PairTy <$> go ctx x <*> go ctx y
--     go ctx (App f x) = do
--       argTy_x <- go ctx x
--       fTy <- go ctx f
--       case fTy of
--         argTy_f :-> resTy -> do
--           liftA2 (:->) (unify argTy_x argTy_f) (pure resTy)
--         _ -> inferError ()

--     go ctx (Lam f) = do
--       n <- newExprName

--       let v = Var n
--           body = instantiate1 v f

--       tv <- TyVar <$> newCtName

--       resTy <- go ((n, tv) : ctx) body
--       pure (tv :-> resTy)

--     go ctx (Var x) =
--       case lookup x ctx of
--         Nothing -> TyVar <$> newCtName
--         Just ty -> pure ty

