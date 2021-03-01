-----------------------------------------------------
-- Copyright 2020, <anonymous>
-- Closely based on the Ev.Eff library.
-----------------------------------------------------
{-# LANGUAGE  TypeOperators,            -- h :* e                     (looks nice but not required)
              ConstraintKinds,          -- type (h ?: e) = In h e     (looks nice but not required)
              FlexibleInstances,        -- instance Sub () e          (non type variable in head)
              FlexibleContexts,         -- (State Int ?: e) => ...    (non type variable argument)
              DataKinds, TypeFamilies,  -- type family HEqual h h' :: Bool
              UndecidableInstances,     -- InEq (HEqual h h') h h' e => ... (duplicate instance variable)
              ScopedTypeVariables,
              GADTs,
              MultiParamTypeClasses,
              Rank2Types
#-}
module Control.Mp.Eff(
            -- * Effect monad
              Eff
            , runEff          -- :: Eff () a -> a

            -- * Effect context
            , (:?)            -- h :? e,  is h in e?
            , (:*)            -- h :* e,  cons h in front of e
            -- , In           -- alias for :?

            -- * Perform and Handlers
            , perform         -- :: (h :? e) => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
            , handler         -- :: h e ans -> Eff (h :* e) ans -> Eff e ans
            , handlerRet      -- :: (ans -> b) -> h e b -> Eff (h :* e) ans -> Eff e b
            , handlerHide     -- :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
            , mask            -- :: Eff e ans -> Eff (h :* e) ans

            -- * Defining operations
            , Op
            , value           -- :: a -> Op () a e ans
            , function        -- :: (a -> Eff e b) -> Op a b e ans
            , except          -- :: (a -> Eff e ans) -> Op a b e ans
            , operation       -- :: (a -> (b -> Eff e ans)) -> Op a b e ans

            -- * Local state
            , Local           -- Local a e ans

            , local           -- :: a -> Eff (Local a :* e) ans -> Eff e ans
            , localRet        -- :: a -> (ans -> a -> b) -> Eff (Local a :* e) ans -> Eff e b
            , handlerLocal    -- :: a -> h (Local a :* e) ans -> Eff (h :* e) ans -> Eff e ans
            , handlerLocalRet -- :: a -> (ans -> a -> b) -> h (Local a :* e) b -> Eff (h :* e) ans -> Eff e b

            , lget            -- :: (Local a :? e) => Eff e a
            , lput            -- :: (Local a :? e) => a -> Eff e ()
            , lmodify         -- :: (Local a :? e) => (a -> a) -> Eff e ()

            , localGet        -- :: Eff (Local a :* e) a
            , localPut        -- :: a -> Eff (Local a :* e) ()
            , localModify     -- :: (a -> a) -> Eff (Local a :* e) a

            ) where

import Prelude hiding (read,flip)
import Control.Monad( ap, liftM )
import Data.Type.Equality( (:~:)( Refl ) )
import Control.Monad.Primitive
-- import Debug.Trace( trace )

-------------------------------------------------------
-- Assume some way to generate a fresh prompt marker
-- associated with specific effect and answer type.
-------------------------------------------------------
import Unsafe.Coerce     (unsafeCoerce)
import System.IO.Unsafe ( unsafePerformIO )
import Data.IORef

-- an abstract marker
data Marker (h:: * -> * -> *) e a = Marker !Integer

instance Show (Marker h e a) where
  show (Marker i) = show i

-- if markers match, their types are the same
mmatch :: Marker h e a -> Marker h' e' b -> Maybe ((h e a, a, e) :~: (h' e' b, b, e'))
mmatch (Marker i) (Marker j) | i == j  = Just (unsafeCoerce Refl)
mmatch _ _ = Nothing

unique :: IORef Integer
unique = unsafePerformIO (newIORef 0)

-- evaluate a action with a fresh marker
freshMarker :: (Marker h e a -> Eff e a) -> Eff e a
freshMarker f
  = let m = unsafePerformIO $
            do i <- readIORef unique;
               writeIORef unique (i+1);
               return i
    in seq m (f (Marker m))

-- evaluate a action with a fresh marker
freshMarkerCtl :: (Marker h e a -> Ctl e a) -> Ctl e a
freshMarkerCtl f
  = let m = unsafePerformIO $
            do i <- readIORef unique;
               writeIORef unique (i+1);
               return i
    in seq m (f (Marker m))

-------------------------------------------------------
-- The handler context
-------------------------------------------------------
infixr 5 :*

data (h :: * -> * -> *) :* e

data Context e where
  CCons :: !(Marker h e' ans) -> !(h e' ans) -> !(ContextT e e') -> !(Context e) -> Context (h :* e)
  CNil  :: Context ()

data ContextT e e' where
  CTCons :: !(Marker h e' ans) -> !(h e' ans) -> !(ContextT e e') -> ContextT e (h :* e)
  CTId   :: ContextT e e
  -- CTFun :: !(Context e -> Context e') -> ContextT e e'

-- apply a context transformer
applyT :: ContextT e e' -> Context e -> Context e'
applyT (CTCons m h g) ctx = CCons m h g ctx
applyT (CTId) ctx         = ctx
--applyT (CTFun f) ctx = f ctx

-- the tail of a context
ctail :: Context (h :* e) -> Context e
ctail (CCons _ _ _ ctx)   = ctx

-------------------------------------------------------
-- The Multi Prompt control monad
-- ans: the answer type, i.e. the type of the handler/prompt context.
-- e' : the answer effect, i.e. the effect in the handler/prompt context.
-- b  : the result type of the operation
-------------------------------------------------------
data Ctl e a = Pure { result :: !a }
             | forall h b e' ans.
               Control{ marker :: Marker h e' ans,                    -- prompt marker to yield to (in type context `::ans`)
                        op     :: !((b -> Eff e' ans) -> Eff e' ans),  -- the final action, just needs the resumption (:: b -> Eff e' ans) to be evaluated.
                        cont   :: !(b -> Eff e a) }                    -- the (partially) build up resumption; (b -> Eff e a) :~: (b -> Eff e' ans)` by the time we reach the prompt


newtype Eff e a = Eff { unEff :: Context e -> Ctl e a }

lift :: Ctl e a -> Eff e a
lift ctl = Eff (\ctx -> ctl)

under :: In h e => Marker h e' ans -> Context e' -> Eff e' b -> Eff e b
under m ctx (Eff eff) = Eff (\_ -> case eff ctx of
                                       Pure x -> Pure x
                                       Control n op cont -> Control n op (resumeUnder m ctx cont))
                                       -- Control n op cont -> Control n op (under m ctx . cont)) -- wrong

resumeUnder :: forall h a b e e' ans. In h e => Marker h e' ans -> Context e' -> (b -> Eff e' a) -> (b -> Eff e a)
resumeUnder m ctx cont x
  = withSubContext $ \(SubContext (CCons m' h' g' ctx') :: SubContext h) ->
    case mmatch m m' of
      Just Refl -> under m (applyT g' ctx') (cont x)
      Nothing   -> error "EffEv.resumeUnder: marker does not match anymore (this should never happen?)"


instance Functor (Eff e) where
  fmap  = liftM
instance Applicative (Eff e) where
  pure  = return
  (<*>) = ap
instance Monad (Eff e) where
  return x   = Eff (\evv -> Pure x)
  (>>=)      = bind

-- start yielding (with an initially empty continuation)
{-# INLINE yield #-}
yield :: Marker h e ans -> ((b -> Eff e ans) -> Eff e ans) -> Eff e' b
yield m op  = Eff (\ctx -> Control m op pure)

{-# INLINE kcompose #-}
kcompose :: (b -> Eff e c) -> (a -> Eff e b) -> a -> Eff e c      -- Kleisli composition
kcompose g f x =
  case f x of
    -- bind (f x) g
    Eff eff -> Eff (\ctx -> case eff ctx of
                              Pure x -> unEff (g x) ctx
                              Control m op cont -> Control m op (g `kcompose` cont))

{-# INLINE bind #-}
bind :: Eff e a -> (a -> Eff e b) -> Eff e b
bind (Eff eff) f
  = Eff (\ctx -> case eff ctx of
                   Pure x            -> unEff (f x) ctx
                   Control m op cont -> Control m op (f `kcompose` cont))  -- keep yielding with an extended continuation

instance Functor (Ctl e) where
  fmap  = liftM
instance Applicative (Ctl e) where
  pure  = return
  (<*>) = ap
instance Monad (Ctl e) where
  return x      = Pure x
  Pure x >>= f  = f x
  (Control m op cont) >>= f
    = Control m op (f `kcompose2` cont)

kcompose2 :: (b -> Ctl e c) -> (a -> Eff e b) -> a -> Eff e c
kcompose2 g f x
  = Eff $ \ctx -> case unEff (f x) ctx of
        Pure x -> g x
        Control m op cont -> Control m op (g `kcompose2` cont)


-- use a prompt with a unique marker (and handle yields to it)
{-# INLINE prompt #-}
prompt :: Marker h e ans -> h e ans -> Eff (h :* e) ans -> Eff e ans
prompt m h (Eff eff) = Eff $ \ctx ->
  case (eff (CCons m h CTId ctx)) of                    -- add handler o the context
    Pure x -> Pure x
    Control n op cont ->
        let cont' x = prompt m h (cont x) in      -- extend the continuation with our own prompt
        case mmatch m n of
          Nothing   -> Control n op cont'          -- keep yielding (but with the extended continuation)
          Just Refl -> unEff (op cont') ctx   -- found our prompt, invoke `op` (under the context `ctx`).
                              -- Note: `Refl` proves `a ~ ans` and `e ~ e'` (the existential `ans,e'` in Control)

{-# INLINE handler #-}
handler :: h e ans -> Eff (h :* e) ans -> Eff e ans
handler h action
  = freshMarker $ \m -> prompt m h action

-- Run a control monad
runEff :: Eff () a -> a
runEff (Eff eff) = case eff CNil of
                   Pure x -> x
                   Control _ _ _ -> error "Unhandled operation"  -- can never happen

{-# INLINE handlerRet #-}
handlerRet :: (ans -> a) -> h e a -> Eff (h :* e) ans -> Eff e a
handlerRet ret h action
  = handler h (do x <- action; return (ret x))

{-# INLINE handlerHide #-}
handlerHide :: h (h' :* e) ans -> Eff (h :* e) ans -> Eff (h' :* e) ans
handlerHide h action
  = freshMarker (\m ->
      Eff (\(CCons m' h' g' ctx') ->
              ctlHide h (unEff action (CCons m h (CTCons m' h' g') ctx'))))

{-# INLINE ctlHide #-}
ctlHide :: h (h' :* e) ans -> Ctl (h :* e) ans -> Ctl (h' :* e) ans
ctlHide h (Pure x) = Pure x
ctlHide h (Control m op cont) = Control m op (\b -> handlerHide h (cont b))

reflect :: Eff e a -> Eff e (Ctl e a)
reflect (Eff eff) = Eff (\ctx -> let ctl = eff ctx in seq ctl (Pure ctl))

{-# INLINE handlerHideRetEff #-}
handlerHideRetEff :: (ans -> Eff (h' :* e) b) -> h (h' :* e) b -> Eff (h :* e) ans -> Eff (h' :* e) b
handlerHideRetEff ret h action
  = freshMarker (\m -> Eff (\ctx@(CCons m' h' g' ctx') ->
                              ctlHideRet ret h ctx $ unEff action (CCons m h (CTCons m' h' g') ctx')))

{-# INLINE ctlHideRet #-}
ctlHideRet :: (ans -> Eff (h' :* e) b) -> h (h' :* e) b -> Context (h' :* e) -> Ctl (h :* e) ans ->  Ctl (h' :* e) b
ctlHideRet ret h ctx (Pure x) = unEff (ret x) ctx
ctlHideRet ret h ctx (Control m op cont) = Control m op (\b -> handlerHideRetEff ret h (cont b))

-- | Mask the top effect handler in the give action (i.e. if a operation is performed
-- on an @h@ effect inside @e@ the top handler is ignored).
mask :: Eff e ans -> Eff (h :* e) ans
mask (Eff f) = Eff (\ctx -> maskCtl (f (ctail ctx)))

maskCtl :: Ctl e ans -> Ctl (h :* e) ans
maskCtl (Pure x) = Pure x
maskCtl (Control m op cont) = Control m op (\b -> mask (cont b))

---------------------------------------------------------
--
---------------------------------------------------------

type h :? e = In h e

data SubContext h = forall e. SubContext !(Context (h:* e))

class In h e where
  subContext :: Context e -> SubContext h

instance (InEq (HEqual h h') h h' ctx) => In h (h' :* ctx)  where
  subContext = subContextEq

type family HEqual (h :: * -> * -> *) (h' :: * -> * -> *) :: Bool where
  HEqual h h  = 'True
  HEqual h h' = 'False

class (iseq ~ HEqual h h') => InEq iseq h h' e  where
  subContextEq :: Context (h' :* e) -> SubContext h

instance (h ~ h') => InEq 'True h h' e where
  subContextEq ctx = SubContext ctx

instance ('False ~ HEqual h h', In h e) => InEq 'False h h' e where
  subContextEq ctx = subContext (ctail ctx)


{-# INLINE withSubContext #-}
withSubContext :: (h :? e) => (SubContext h -> Eff e a) -> Eff e a
withSubContext action
  = do ctx <- Eff Pure
       action (subContext ctx)


------------------------------------
-- Operations
-------------------------------------

-- | The abstract type of operations of type @a@ to @b@, for a handler
-- defined in an effect context @e@ and answer type @ans@.
data Op a b e ans = Op { applyOp:: !(forall h e'. In h e' => Marker h e ans -> Context e -> a -> Eff e' b) }


-- Given evidence and an operation selector, perform the operation
{-# INLINE perform #-}
perform :: In h e => (forall e' ans. h e' ans -> Op a b e' ans) -> a -> Eff e b
perform selectOp x
  = withSubContext $ \(SubContext (CCons m h g ctx)) ->
      applyOp (selectOp h) m (applyT g ctx) x

-- | Create an operation that always resumes with a constant value (of type @a@).
-- (see also the `perform` example).
value :: a -> Op () a e ans
value x = function (\() -> return x)

-- | Create an operation that takes an argument of type @a@ and always resumes with a result of type @b@.
-- These are called /tail-resumptive/ operations and are implemented more efficient than
-- general operations as they can execute /in-place/ (instead of yielding to the handler).
-- Most operations are tail-resumptive. (See also the `handlerLocal` example).
function :: (a -> Eff e b) -> Op a b e ans
function f = Op (\m ctx x -> under m ctx (f x))

-- | Create an fully general operation from type @a@ to @b@.
-- the function @f@ takes the argument, and a /resumption/ function of type @b -> `Eff` e ans@
-- that can be called to resume from the original call site. For example:
--
-- @
-- data Amb e ans = Amb { flip :: forall b. `Op` () Bool e ans }
--
-- xor :: (Amb `:?` e) => `Eff` e Bool
-- xor = do x <- `perform` flip ()
--          y <- `perform` flip ()
--          return ((x && not y) || (not x && y))
--
-- solutions :: `Eff` (Amb `:*` e) a -> `Eff` e [a]
-- solutions = `handlerRet` (\\x -> [x]) $
--             Amb{ flip = `operation` (\\() k -> do{ xs <- k True; ys <- k False; return (xs ++ ys)) }) }
-- @
operation :: (a -> (b -> Eff e ans) -> Eff e ans) -> Op a b e ans
operation f = Op (\m ctx x -> yield m (\ctlk -> f x ctlk))


-- | Create an operation that never resumes (an exception).
-- (See `handlerRet` for an example).
except :: (a -> Eff e ans) -> Op a b e ans
except f = Op (\m ctx x -> yield m (\ctlk -> f x))

--------------------------------------------------------------------------------
-- Efficient (and safe) Local state handler
--------------------------------------------------------------------------------
-- | The type of the built-in state effect.
-- (This state is generally more efficient than rolling your own and usually
-- used in combination with `handlerLocal` to provide local isolated state)
newtype Local a e ans = Local (IORef a)

-- | Unsafe `IO` in the `Eff` monad.
{-# INLINE unsafeIO #-}
unsafeIO :: IO a -> Eff e a
unsafeIO io = let x = unsafeInlinePrim io in seq x (Eff $ \_ -> Pure x)

{-# INLINE unsafeIOCtl #-}
unsafeIOCtl :: IO a -> Ctl e a
unsafeIOCtl io = let x = unsafeInlinePrim io in seq x (Pure x)

-- | Get the value of the local state.
{-# INLINE lget #-}
lget :: Local a e ans -> Op () a e ans
lget (Local r) = Op (\m ctx x -> unsafeIO (seq x $ readIORef r))

-- | Set the value of the local state.
{-# INLINE lput #-}
lput :: Local a e ans -> Op a () e ans
lput (Local r) = Op (\m ctx x -> unsafeIO (writeIORef r x))

-- | Update the value of the local state.
{-# INLINE lmodify #-}
lmodify :: Local a e ans -> Op (a -> a) () e ans
lmodify (Local r) = Op (\m ctx f -> unsafeIO (do{ x <- readIORef r; writeIORef r $! (f x) }))

-- | Get the value of the local state if it is the top handler.
localGet :: Eff (Local a :* e) a
localGet = perform lget ()

-- | Set the value of the local state if it is the top handler.
localPut :: a -> Eff (Local a :* e) ()
localPut x = perform lput x

-- | Update the value of the local state if it is the top handler.
localModify :: (a -> a) -> Eff (Local a :* e) ()
localModify f = perform lmodify f

-- A special prompt that saves and restores state per resumption
mpromptIORef :: IORef a -> Eff e b -> Eff e b
mpromptIORef r action
  = Eff $ \ctx -> case (unEff action ctx) of
      p@(Pure _) -> p
      Control m op cont
        -> do val <- unsafeIOCtl (readIORef r)                 -- save current value on yielding
              let cont' x = do unsafeIO (writeIORef r val)  -- restore saved value on resume
                               mpromptIORef r (cont x)
              Control m op cont'

mpromptIORefCtl :: IORef a -> Ctl e b -> Ctl e b
mpromptIORefCtl r action
  = case action of
      p@(Pure _) -> p
      Control m op cont
        -> do val <- unsafeIOCtl (readIORef r)                 -- save current value on yielding
              let cont' x = do unsafeIO (writeIORef r val)  -- restore saved value on resume
                               mpromptIORef r (cont x)
              Control m op cont'

-- | Create an `IORef` connected to a prompt. The value of
-- the `IORef` is saved and restored through resumptions.
unsafePromptIORef :: a -> (Marker h e b -> IORef a -> Ctl e b) -> Ctl e b
unsafePromptIORef init action
  = freshMarkerCtl $ \m ->
    do r <- unsafeIOCtl (newIORef init)
       mpromptIORefCtl r (action m r)

-- | Create a local state handler with an initial state of type @a@,
-- with a return function to combine the final result with the final state to a value of type @b@.
{-# INLINE localRet #-}
localRet :: a -> (ans -> a -> b) -> Eff (Local a :* e) ans -> Eff e b
localRet init ret action
  = Eff (\ctx -> unsafePromptIORef init $ \m r ->  -- set a fresh prompt with marker `m`
                 case unEff action (CCons m (Local r) CTId ctx) of-- and call action with the extra evidence
                    Pure x -> do y <- unsafeIOCtl (readIORef r)
                                 return (ret x y)
                    Control m op cont -> Control m op (\b -> localRet init ret (cont b))
        )


-- | Create a local state handler with an initial state of type @a@.
{-# INLINE local #-}
local :: a -> Eff (Local a :* e) ans -> Eff e ans
local init action
 = localRet init const action

-- | Create a new handler for @h@ which can access the /locally isolated state/ @`Local` a@.
-- This is fully local to the handler @h@ only and not visible in the @action@ as
-- apparent from its effect context (which does /not/ contain @`Local` a@). The
-- @ret@ argument can be used to transform the final result combined with the final state.
{-# INLINE handlerLocalRet #-}
handlerLocalRet :: a -> (ans -> a -> b) -> (h (Local a :* e) b) -> Eff (h :* e) ans -> Eff e b
handlerLocalRet init ret h action
  = local init $ handlerHideRetEff (\x -> do{ y <- localGet; return (ret x y)}) h action

-- | Create a new handler for @h@ which can access the /locally isolated state/ @`Local` a@.
-- This is fully local to the handler @h@ only and not visible in the @action@ as
-- apparent from its effect context (which does /not/ contain @`Local` a@).
--
-- @
-- data State a e ans = State { get :: `Op` () a e ans, put :: `Op` a () e ans  }
--
-- state :: a -> `Eff` (State a `:*` e) ans -> `Eff` e ans
-- state init = `handlerLocal` init (State{ get = `function` (\\_ -> `perform` `lget` ()),
--                                        put = `function` (\\x -> `perform` `lput` x) })
--
-- test = `runEff` $
--        state (41::Int) $
--        inc                -- see `:?`
-- @
{-# INLINE handlerLocal #-}
handlerLocal :: a -> (h (Local a :* e) ans) -> Eff (h :* e) ans -> Eff e ans
handlerLocal init h action
  = local init (handlerHide h action)
